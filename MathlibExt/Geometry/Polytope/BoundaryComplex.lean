/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Geometry.Polytope.Faces
public import MathlibExt.Combinatorics.SimplicialSphereShared
import Mathlib.Analysis.Convex.GaugeRescale
import Mathlib.Analysis.Convex.Intrinsic
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# The boundary complex of a simplicial polytope

The proper faces of a full-dimensional simplicial polytope realize a finite simplicial sphere
with the same face numbers below the dimension of the polytope.

S. Klee and I. Novik state the boundary-sphere result in all dimensions and identify the face
numbers in *Face enumeration on simplicial complexes*, §2 (arXiv:1505.06380). G. M. Ziegler
describes boundaries of convex 4-polytopes as strongly regular cellulations of the 3-sphere in
*Face numbers of 4-polytopes and 3-spheres*, Proc. ICM 2002, §3 (arXiv:math/0208073v2).
His reference [29] is *Lectures on Polytopes*, Graduate Texts in Mathematics 152.
-/

public section

open Set

namespace MathlibExt.Geometry.Polytope.FaceNumbersWanted

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {s : Finset E} {F : Set E}

private abbrev hull (s : Finset E) := convexHull ℝ (s : Set E)

private theorem span_full (hfull : (interior (hull s)).Nonempty) :
    affineSpan ℝ (s : Set E) = ⊤ := by
  simpa only [hull, affineSpan_convexHull] using
    (convex_convexHull ℝ (s : Set E)).interior_nonempty_iff_affineSpan_eq_top.mp hfull

/-- Interpolate a functional constant on the prescribed set and larger at a given point. -/
private theorem separator {T : Set E} {a z : E} (ha : a ∈ T) (hz : z ∉ affineSpan ℝ T) :
    ∃ g : StrongDual ℝ E, (∀ v ∈ T, g v = g a) ∧ g a < g z := by
  have hza : z - a ∉ (affineSpan ℝ T).direction := fun h =>
    hz ((AffineSubspace.vsub_right_mem_direction_iff_mem (mem_affineSpan ℝ ha) z).1 h)
  obtain ⟨f, hf, hfz⟩ := LinearMap.exists_extend_of_notMem
    (0 : (affineSpan ℝ T).direction →ₗ[ℝ] ℝ) hza 1
  refine ⟨f.toContinuousLinearMap, ?_, ?_⟩
  · intro v hv
    have hm := vsub_mem_vectorSpan ℝ hv ha
    rw [← direction_affineSpan] at hm
    have he := DFunLike.congr_fun hf ⟨v - a, hm⟩
    change f (v - a) = 0 at he
    exact sub_eq_zero.mp ((map_sub f v a).symm.trans he)
  · change f a < f z
    rw [map_sub] at hfz
    linarith

/-- A face of codimension at least two can be enlarged while remaining proper.
Tilt its exposing functional until a further generator first reaches the supporting hyperplane.
One generator outside the face is kept strictly below the hyperplane throughout. -/
private theorem enlarge_face (hfull : (interior (hull s)).Nonempty)
    (hF : F ∈ faces s) (hne : F.Nonempty) (hproper : F ≠ hull s)
    (hd : Module.finrank ℝ (vectorSpan ℝ F) + 1 < Module.finrank ℝ E) :
    ∃ G ∈ faces s, F ⊂ G ∧ G ≠ hull s := by
  classical
  obtain ⟨a, ha⟩ := hne
  obtain ⟨f, hfeq⟩ := hF ⟨a, ha⟩
  change F = f.toExposed (hull s) at hfeq
  have hmax : ∀ v ∈ hull s, f v ≤ f a := ((hfeq ▸ ha : a ∈ f.toExposed (hull s))).2
  have hmem {v : E} (hv : v ∈ hull s) : v ∈ F ↔ f v = f a := by
    rw [hfeq]
    exact ⟨fun h => (hmax v hv).antisymm (h.2 a (hF.subset ha)),
      fun h => ⟨hv, fun w hw => h ▸ hmax w hw⟩⟩
  obtain ⟨y, hys, hy⟩ : ∃ y ∈ s, y ∉ F := by
    by_contra! h
    exact hproper (hF.subset.antisymm (convexHull_min h (hF.convex (convex_convexHull ℝ _))))
  let T := insert y F
  have hT : affineSpan ℝ T ≠ ⊤ := by
    intro e
    have h := finrank_vectorSpan_insert_le_set ℝ F y
    change Module.finrank ℝ (vectorSpan ℝ T) ≤ _ at h
    rw [← direction_affineSpan, e, AffineSubspace.direction_top, finrank_top] at h
    omega
  obtain ⟨z, hzs, hz⟩ : ∃ z ∈ s, z ∉ affineSpan ℝ T := by
    by_contra! h
    exact hT (top_unique (span_full hfull ▸ (affineSpan_le.2 h)))
  obtain ⟨g, hg, hgz⟩ := separator (mem_insert_of_mem y ha) hz
  let above := s.filter fun v => g a < g v
  have habove : z ∈ above := Finset.mem_filter.2 ⟨hzs, hgz⟩
  let ratio := fun v => (f a - f v) / (g v - g a)
  obtain ⟨b, hb, hmin⟩ := above.exists_min_image ratio ⟨z, habove⟩
  obtain ⟨hbs, hgb⟩ := Finset.mem_filter.1 hb
  have hbf : b ∉ F := fun h => hgb.ne' (hg b (mem_insert_of_mem _ h))
  have hsP : (s : Set E) ⊆ hull s := subset_convexHull ℝ _
  have hfb := lt_of_le_of_ne (hmax b (hsP hbs)) (mt (hmem (hsP hbs)).mpr hbf)
  let c := ratio b
  have hc : 0 < c := div_pos (sub_pos.2 hfb) (sub_pos.2 hgb)
  let l := f + c • g
  have hl (v : E) : l v = f v + c * g v := rfl
  have hle : ∀ v ∈ s, l v ≤ l a := by
    intro v hv
    simp only [hl]
    by_cases hgv : g a < g v
    · have := (le_div_iff₀ (sub_pos.2 hgv)).1 (hmin v (Finset.mem_filter.2 ⟨hv, hgv⟩))
      change c * (g v - g a) ≤ f a - f v at this
      linarith
    · exact add_le_add (hmax v (hsP hv)) (mul_le_mul_of_nonneg_left (le_of_not_gt hgv) hc.le)
  have hleP : ∀ v ∈ hull s, l v ≤ l a :=
    fun _ hv => convexHull_min (t := {w | l w ≤ l a}) hle
      (convex_halfSpace_le l.toLinearMap.isLinear _) hv
  let G := l.toExposed (hull s)
  have hG {v : E} (hv : v ∈ hull s) : v ∈ G ↔ l v = l a :=
    ⟨fun h => (hleP v hv).antisymm (h.2 a (hF.subset ha)),
      fun h => ⟨hv, fun w hw => h ▸ hleP w hw⟩⟩
  have hbG : b ∈ G := by
    apply (hG (hsP hbs)).2
    have h : c * (g b - g a) = f a - f b := div_mul_cancel₀ _ (sub_ne_zero.mpr hgb.ne')
    simp only [hl]
    linarith
  refine ⟨G, ContinuousLinearMap.toExposed.isExposed,
    ⟨fun v hv => (hG (hF.subset hv)).2 ?_, fun h => hbf (h hbG)⟩, ?_⟩
  · rw [hl, hl, (hmem (hF.subset hv)).1 hv, hg v (mem_insert_of_mem _ hv)]
  · intro e
    have hyG := (hG (hsP hys)).1 (e.symm ▸ hsP hys)
    rw [hl, hl, hg y (mem_insert _ _)] at hyG
    exact hy ((hmem (hsP hys)).2 (by linarith))


omit [FiniteDimensional ℝ E] in
private theorem proper_face_subset_frontier (hF : F ∈ faces s) (hp : F ≠ hull s) :
    F ⊆ frontier (hull s) := by
  intro x hx
  refine ⟨subset_closure (hF.subset hx), fun hi => ?_⟩
  obtain ⟨l, hl⟩ := hF ⟨x, hx⟩
  have hm : IsMaxOn l (hull s) x := isMaxOn_iff.2 ((hl ▸ hx).2)
  have hz := (hm.isLocalMax (mem_interior_iff_mem_nhds.mp hi)).hasFDerivAt_eq_zero l.hasFDerivAt
  apply hp
  simpa [hz] using hl

omit [FiniteDimensional ℝ E] in
private theorem exists_proper_face_of_mem_frontier (hfull : (interior (hull s)).Nonempty)
    {x : E} (hx : x ∈ frontier (hull s)) : ∃ F ∈ faces s, F ≠ hull s ∧ x ∈ F := by
  obtain ⟨f, hf, hmax⟩ := geometric_hahn_banach_of_nonempty_interior_point
    (convex_convexHull ℝ _) hx.2 hfull
  refine ⟨f.toExposed (hull s), ContinuousLinearMap.toExposed.isExposed, ?_,
    (s.finite_toSet.isClosed_convexHull ℝ).frontier_subset hx, hmax⟩
  obtain ⟨a, ha⟩ := hfull
  intro e
  have hm : IsMaxOn f (hull s) a := isMaxOn_iff.2
    (show a ∈ f.toExposed (hull s) from e.symm ▸ interior_subset ha).2
  exact hf ((hm.isLocalMax (mem_interior_iff_mem_nhds.mp ha)).hasFDerivAt_eq_zero f.hasFDerivAt)

private theorem exists_facet (hfull : (interior (hull s)).Nonempty)
    (hF : F ∈ faces s) (hne : F.Nonempty) (hp : F ≠ hull s) :
    ∃ G ∈ faces s, F ⊆ G ∧ Module.finrank ℝ (vectorSpan ℝ G) + 1 = Module.finrank ℝ E := by
  let A := {G ∈ faces s | G ≠ hull s}
  have hfin : A.Finite := (faces_finite s).subset (fun _ h => h.1)
  obtain ⟨G, hFG, hG⟩ := hfin.exists_le_maximal (show F ∈ A from ⟨hF, hp⟩)
  have hneG := hne.mono hFG
  obtain ⟨hface, hprop⟩ := hG.prop
  refine ⟨G, hface, hFG, le_antisymm ?_ ?_⟩
  · by_contra! h
    have he : (affineSpan ℝ G).direction = ⊤ := Submodule.eq_top_of_finrank_eq (by
      rw [direction_affineSpan]
      exact le_antisymm (Submodule.finrank_le _) (by omega))
    have hi := (hface.convex (convex_convexHull ℝ _)).interior_nonempty_iff_affineSpan_eq_top.mpr
      ((AffineSubspace.direction_eq_top_iff_of_nonempty (hneG.mono (subset_affineSpan ℝ _))).mp he)
    obtain ⟨x, hx⟩ := hi
    exact (proper_face_subset_frontier hface hprop (interior_subset hx)).2
      (interior_mono hface.subset hx)
  · by_contra! h
    obtain ⟨H, hH, hGH, hHp⟩ := enlarge_face hfull hface hneG hprop h
    exact hGH.not_ge (hG.le_of_ge ⟨hH, hHp⟩ hGH.le)

private noncomputable def faceVerts (s : Finset E) (F : Set E) : Finset E :=
  ((extremePoints_finite s).inter_of_right F).toFinset

omit [FiniteDimensional ℝ E] in
private theorem coe_faceVerts : (faceVerts s F : Set E) = F ∩ (hull s).extremePoints ℝ :=
  Set.Finite.coe_toFinset _

omit [FiniteDimensional ℝ E] in
private theorem hull_faceVerts (hF : F ∈ faces s) : hull (faceVerts s F) = F := by
  rw [hull, coe_faceVerts, ← hF.isExtreme.extremePoints_eq]
  have h := closure_convexHull_extremePoints (hF.isCompact (s.finite_toSet.isCompact_convexHull ℝ))
    (hF.convex (convex_convexHull ℝ _))
  have hf := (extremePoints_finite s).subset hF.isExtreme.extremePoints_subset_extremePoints
  rwa [(hf.isClosed_convexHull ℝ).closure_eq] at h

private theorem indep_faceVerts (hfull : (interior (hull s)).Nonempty) (hsimp : IsSimplicial s)
    (hF : F ∈ faces s) (hne : F.Nonempty) (hp : F ≠ hull s) :
    AffineIndependent ℝ ((↑) : faceVerts s F → E) := by
  obtain ⟨G, hG, hFG, hdim⟩ := exists_facet hfull hF hne hp
  have hds : dim s = Module.finrank ℝ E := by
    rw [dim, affineSpan_convexHull, span_full hfull, AffineSubspace.direction_top, finrank_top]
  have hc := hsimp G hG (hne.mono hFG) (by rw [direction_affineSpan, hds]; exact hdim)
  have hcard : Fintype.card (faceVerts s G) = Module.finrank ℝ (vectorSpan ℝ G) + 1 := by
    rw [Fintype.card_coe, ← Set.ncard_coe_finset, coe_faceVerts, hc, hds, hdim]
  have hi : AffineIndependent ℝ ((↑) : faceVerts s G → E) := by
    apply (affineIndependent_iff_finrank_vectorSpan_eq ℝ _ hcard).mpr
    apply congrArg (fun V : Submodule ℝ E => Module.finrank ℝ V)
    rw [Subtype.range_coe, ← direction_affineSpan, ← affineSpan_convexHull]
    change (affineSpan ℝ (hull (faceVerts s G))).direction = _
    rw [hull_faceVerts hG, direction_affineSpan]
  apply hi.mono
  rw [coe_faceVerts, coe_faceVerts]
  exact inter_subset_inter_left _ hFG


/-- The sum of the selected barycentric coordinates exposes a subsimplex. -/
private theorem exposed_subsimplex {u t : Finset E} (hi : AffineIndependent ℝ ((↑) : u → E))
    (htu : t ⊆ u) : IsExposed ℝ (hull u) (hull t) := by
  classical
  obtain ⟨B, huB, hBi, hBtop⟩ := exists_subset_affineIndependent_affineSpan_eq_top hi
  let b : AffineBasis B ℝ E := ⟨Subtype.val, hBi, by simpa using hBtop⟩
  let J := t.subtype (· ∈ B)
  let A (v : E) := ∑ i ∈ J, b.coord i v
  have hA (v : E) (hv : v ∈ u) : A v = if v ∈ t then 1 else 0 := by
    change (∑ i ∈ J, b.coord i (b ⟨v, huB hv⟩)) = _
    simp [AffineBasis.coord_apply, J]
  let l : StrongDual ℝ E := ∑ i ∈ J, (b.coord i).linear.toContinuousLinearMap
  have hl (v : E) : l v = A v - A 0 := by
    simp only [l, sum_apply, A, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => congrFun (b.coord i).decomp' v
  refine isExposed_convexHull_of_forall_le u t l (1 - A 0) ?_ ?_ ?_
  · intro v hv
    simp only [hl, hA v hv]
    split <;> linarith
  · intro v hv
    exact ⟨htu hv, by simp [hl, hA v (htu hv), (show v ∈ t from hv)]⟩
  · intro v hv he
    by_contra hn
    change v ∉ t at hn
    simp only [hl, hA v hv, hn, ite_false] at he
    linarith

/-- **Boundary complex of a simplicial polytope.** For a full-dimensional simplicial polytope
generated by a finite set of points, the simplices are the vertex sets of its nonempty proper faces.

Source: S. Klee and I. Novik, *Face enumeration on simplicial complexes*, §2 (arXiv:1505.06380). -/
noncomputable def boundaryComplex (hfull : (interior (convexHull ℝ (s : Set E))).Nonempty)
    (hsimp : IsSimplicial s) : Geometry.SimplicialComplex ℝ E where
  faces := {t | ∃ F ∈ faces s, F.Nonempty ∧ F ≠ hull s ∧ t = faceVerts s F}
  indep := by
    rintro t ⟨F, hF, hne, hp, rfl⟩
    exact indep_faceVerts hfull hsimp hF hne hp
  isRelLowerSet_faces := by
    rintro u ⟨F, hF, hne, hp, rfl⟩
    refine ⟨?_, ?_⟩
    · exact Finset.coe_nonempty.mp (convexHull_nonempty_iff.mp ((hull_faceVerts hF).symm ▸ hne))
    · intro t htu ht
      have he := exposed_subsimplex (indep_faceVerts hfull hsimp hF hne hp) htu
      rw [hull_faceVerts hF] at he
      have htF := mem_faces_of_isExposed hF he
      refine ⟨hull t, htF, ht.to_set.mono (subset_convexHull ℝ _),
        fun e => hp (hF.subset.antisymm (e.ge.trans he.subset)), ?_⟩
      apply Finset.coe_injective
      rw [coe_faceVerts, ← htF.isExtreme.extremePoints_eq]
      refine Subset.antisymm ?_ extremePoints_convexHull_subset
      intro v hv
      have hvu : v ∈ (faceVerts s F : Set E) := htu hv
      rw [coe_faceVerts] at hvu
      exact inter_extremePoints_subset_extremePoints_of_subset htF.subset
        ⟨subset_convexHull ℝ _ hv, hvu.2⟩
  inter_subset_convexHull := by
    rintro _ _ ⟨F, hF, -, -, rfl⟩ ⟨G, hG, -, -, rfl⟩
    change hull (faceVerts s F) ∩ hull (faceVerts s G) ⊆ _
    rw [hull_faceVerts hF, hull_faceVerts hG, ← hull_faceVerts (hF.inter hG)]
    apply convexHull_mono
    simp only [coe_faceVerts]
    exact fun _ h => ⟨⟨h.1.1, h.2⟩, ⟨h.1.2, h.2⟩⟩

/-- **Realization of the boundary complex.** The simplices of the boundary complex of a
full-dimensional simplicial polytope cover exactly its topological boundary.

Source: S. Klee and I. Novik, *Face enumeration on simplicial complexes*, §2 (arXiv:1505.06380). -/
theorem boundary_space (hfull : (interior (convexHull ℝ (s : Set E))).Nonempty)
    (hsimp : IsSimplicial s) :
    (boundaryComplex hfull hsimp).space = frontier (convexHull ℝ (s : Set E)) := by
  ext x
  rw [Geometry.SimplicialComplex.mem_space_iff]
  constructor
  · rintro ⟨_, ⟨F, hF, -, hp, rfl⟩, hx⟩
    exact proper_face_subset_frontier hF hp (hull_faceVerts hF ▸ hx)
  · intro hx
    obtain ⟨F, hF, hp, hxF⟩ := exists_proper_face_of_mem_frontier hfull hx
    refine ⟨faceVerts s F, ⟨F, hF, ⟨x, hxF⟩, hp, rfl⟩, ?_⟩
    change x ∈ hull (faceVerts s F)
    rwa [hull_faceVerts hF]


private theorem faceVerts_card (hfull : (interior (hull s)).Nonempty) (hsimp : IsSimplicial s)
    (hF : F ∈ faces s) (hne : F.Nonempty) (hp : F ≠ hull s) :
    (faceVerts s F).card = Module.finrank ℝ (affineSpan ℝ F).direction + 1 := by
  have hi := indep_faceVerts hfull hsimp hF hne hp
  have hn : (faceVerts s F).Nonempty :=
    Finset.coe_nonempty.mp (convexHull_nonempty_iff.mp ((hull_faceVerts hF).symm ▸ hne))
  have := hn.to_subtype
  have he : vectorSpan ℝ (range ((↑) : faceVerts s F → E)) = (affineSpan ℝ F).direction := by
    rw [Subtype.range_coe, ← direction_affineSpan, ← affineSpan_convexHull]
    exact congrArg (fun G : Set E => (affineSpan ℝ G).direction) (hull_faceVerts hF)
  rw [← Fintype.card_coe]
  exact hi.finrank_vectorSpan_add_one.symm.trans
    (congrArg (fun V : Submodule ℝ E => Module.finrank ℝ V + 1) he)

open MathlibExt.Combinatorics.SimplicialSphereShared

/-- **The boundary complex of a simplicial polytope is a simplicial sphere.** If `P = conv s` is a
full-dimensional simplicial polytope in `ℝ^d`, then there is a finite simplicial `(d-1)`-sphere
`X` in `ℝ^d` with the same face numbers as `P`: `f_k(X) = f_k(P)` for every `k < d`. The
boundary complex of `P`, whose simplices are the proper faces of `P`, is such a sphere; the
statement asserts only the existence of `X` with these face numbers, which is what is needed to
transfer the Dehn–Sommerville equations for simplicial spheres to simplicial polytopes. -/
theorem exists_simplicialSphere_faceCount_eq {d : ℕ}
    (s : Finset (EuclideanSpace ℝ (Fin d)))
    (hfull : (interior (convexHull ℝ (s : Set (EuclideanSpace ℝ (Fin d))))).Nonempty)
    (hsimp : IsSimplicial s) :
    ∃ X : FiniteSimplicialSphere d, ∀ k < d, faceCount X k = faceNumber s k := by
  let K := boundaryComplex hfull hsimp
  have hfin : K.faces.Finite := ((faces_finite s).image (faceVerts s)).subset (by
    rintro _ ⟨F, hF, -, -, rfl⟩
    exact ⟨F, hF, rfl⟩)
  obtain ⟨e, -, -, he⟩ := exists_homeomorph_image_interior_closure_frontier_eq_unitBall
    (convex_convexHull ℝ _) hfull (s.finite_toSet.isCompact_convexHull ℝ).isBounded
  have hspace : e '' K.space = Metric.sphere 0 1 := (boundary_space hfull hsimp) ▸ he
  let X : FiniteSimplicialSphere d :=
    ⟨K, hfin, ⟨(e.image K.space).trans (Homeomorph.setCongr hspace)⟩⟩
  refine ⟨X, fun k hk => ?_⟩
  unfold faceCount faceNumber
  apply Set.ncard_congr (fun t _ => hull t)
  · rintro _ ⟨⟨F, hF, hne, hp, rfl⟩, hcard⟩
    rw [hull_faceVerts hF]
    exact ⟨hF, hne, Nat.add_right_cancel ((faceVerts_card hfull hsimp hF hne hp).symm.trans hcard)⟩
  · rintro _ _ ⟨⟨F, hF, -, -, rfl⟩, -⟩ ⟨⟨G, hG, -, -, rfl⟩, -⟩ heq
    rw [hull_faceVerts hF, hull_faceVerts hG] at heq
    rw [heq]
  · rintro F ⟨hF, hne, hdim⟩
    have hp : F ≠ hull s := by
      rintro rfl
      rw [hull, affineSpan_convexHull, span_full hfull, AffineSubspace.direction_top,
        finrank_top, finrank_euclideanSpace_fin] at hdim
      omega
    exact ⟨faceVerts s F, ⟨⟨F, hF, hne, hp, rfl⟩, by
      rw [faceVerts_card hfull hsimp hF hne hp, hdim]⟩, hull_faceVerts hF⟩

end MathlibExt.Geometry.Polytope.FaceNumbersWanted
