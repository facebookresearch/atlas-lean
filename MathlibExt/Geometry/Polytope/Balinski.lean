/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Geometry.Polytope.Faces
public import MathlibExt.Combinatorics.SimpleGraph.VertexConnectivity
public import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Topology.Order.LeftRightNhds

/-!
# Balinski's theorem

The graph of a nonempty convex polytope is `d`-vertex-connected, where `d` is its affine dimension.
-/

open Set Filter
open scoped Topology

namespace MathlibExt.Geometry.Polytope.GraphWanted

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private abbrev Vertices (s : Finset E) := (convexHull ℝ (s : Set E)).extremePoints ℝ

private abbrev RemainingVertices {s : Finset E} (S : Finset (Vertices s)) :=
  (S : Set (Vertices s))ᶜ

private theorem convexHull_vertices {A : Set E} (hA : A.Finite) :
    convexHull ℝ ((convexHull ℝ A).extremePoints ℝ) = convexHull ℝ A := by
  have hfin := hA.subset (extremePoints_convexHull_subset (𝕜 := ℝ))
  rw [← (hfin.isCompact_convexHull ℝ).isClosed.closure_eq]
  exact closure_convexHull_extremePoints (hA.isCompact_convexHull ℝ) (convex_convexHull ℝ A)

private theorem exists_strict_maximizer_functional {A : Set E} (hA : A.Finite) {x : E}
    (hx : x ∈ (convexHull ℝ A).extremePoints ℝ) :
    ∃ g : StrongDual ℝ E, ∀ y ∈ A, y ≠ x → g y < g x := by
  have hx' := ((convex_convexHull ℝ A).mem_extremePoints_iff_mem_sdiff_convexHull_sdiff.1 hx).2
  have hxout : x ∉ convexHull ℝ (A \ {x}) :=
    fun h => hx' (convexHull_mono (sdiff_subset_sdiff_left (subset_convexHull ℝ A)) h)
  obtain ⟨g, r, hlt, hxr⟩ := geometric_hahn_banach_closed_point
    (convex_convexHull ℝ (A \ {x})) ((hA.sdiff.isCompact_convexHull ℝ).isClosed) hxout
  exact ⟨g, fun y hy hne => (hlt _ (subset_convexHull ℝ _ ⟨hy, hne⟩)).trans hxr⟩

private theorem eq_of_normalized_eq_of_le {P : Set E} (hP : Convex ℝ P)
    {x y z : E} (hx : x ∈ P) (hy : y ∈ P.extremePoints ℝ) (hz : z ∈ P)
    (hyx : y ≠ x) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (h : a⁻¹ • (y - x) = b⁻¹ • (z - x)) : y = z := by
  by_contra hyz
  have hb := ha.trans_le hab
  have hsub : y - x = (a / b) • (z - x) := by
    calc
      y - x = a • (a⁻¹ • (y - x)) := by rw [smul_inv_smul₀ ha.ne']
      _ = (a / b) • (z - x) := by rw [h, smul_smul, div_eq_mul_inv]
  have hseg : y ∈ segment ℝ x z := by
    rw [segment_eq_image']
    exact ⟨a / b, ⟨div_nonneg ha.le hb.le, (div_le_one hb).2 hab⟩, by
      change x + (a / b) • (z - x) = y
      rw [← hsub]; abel⟩
  apply (hP.mem_extremePoints_iff_mem_sdiff_convexHull_sdiff.1 hy).2
  exact segment_subset_convexHull (s := P \ {y}) ⟨hx, Ne.symm hyx⟩ ⟨hz, Ne.symm hyz⟩ hseg

/-- If a linear functional increases from a vertex to any other vertex, it increases along
some edge from that vertex. The normalized directions form a finite cross-section of the
cone of directions from the vertex. Exposing a vertex of this section exposes an edge. -/
private theorem exists_adj_gt {s : Finset E} (f : StrongDual ℝ E) {x y : Vertices s}
    (hxy : f x.val < f y.val) : ∃ z : Vertices s, (graph s).Adj x z ∧ f x.val < f z.val := by
  classical
  let V := Vertices s
  let P := convexHull ℝ (s : Set E)
  have hV : V.Finite := extremePoints_finite s
  have hPV : convexHull ℝ V = P := convexHull_vertices s.finite_toSet
  have hxV : x.val ∈ (convexHull ℝ V).extremePoints ℝ := hPV ▸ x.property
  obtain ⟨g, hg⟩ := exists_strict_maximizer_functional hV hxV
  let a (w : E) := g x.val - g w
  let q (w : E) := (a w)⁻¹ • (w - x.val)
  let A := q '' (V \ {x.val})
  have hA : A.Finite := hV.sdiff.image _
  have ha : ∀ w ∈ V \ {x.val}, 0 < a w := fun w hw => sub_pos.2 (hg w hw.1 hw.2)
  have hy : y.val ∈ V \ {x.val} := ⟨y.property, fun h => hxy.ne (congrArg f h).symm⟩
  have hqpos (w : E) (hw : w ∈ V \ {x.val}) :
      0 < f (q w) ↔ f x.val < f w := by
    simp only [q, map_smul, map_sub, smul_eq_mul]
    exact ⟨fun h => sub_pos.1 (pos_of_mul_pos_right h (inv_nonneg.2 (ha w hw).le)),
      fun h => mul_pos (inv_pos.2 (ha w hw)) (sub_pos.2 h)⟩
  obtain ⟨p, hp, hfp⟩ :
      ∃ p ∈ (convexHull ℝ A).extremePoints ℝ, 0 < f p := by
    by_contra! h
    have hle : convexHull ℝ ((convexHull ℝ A).extremePoints ℝ) ⊆ {w | f w ≤ 0} :=
      convexHull_min h (convex_halfSpace_le f.toLinearMap.isLinear 0)
    rw [convexHull_vertices hA] at hle
    exact ((hqpos y.val hy).2 hxy).not_ge (hle (subset_convexHull ℝ _ (mem_image_of_mem q hy)))
  obtain ⟨l, hl⟩ := exists_strict_maximizer_functional hA hp
  obtain ⟨z, hz, hzp⟩ := extremePoints_convexHull_subset hp
  let k := l + l p • g
  have hk (w : E) (hw : w ∈ V \ {x.val}) :
      k w - k x.val = a w * (l (q w) - l p) := by
    have hmul : a w * (a w)⁻¹ = 1 := mul_inv_cancel₀ (ha w hw).ne'
    simp only [k, add_apply, smul_apply,
      q, map_smul, map_sub, smul_eq_mul]
    calc
      _ = a w * (a w)⁻¹ * (l w - l x.val) + l p * (g w - g x.val) := by
        rw [hmul]; ring
      _ = _ := by simp only [a]; ring
  have hqinj : InjOn q (V \ {x.val}) := by
    intro u hu w hw heq
    rcases le_total (a u) (a w) with huw | hwu
    · exact eq_of_normalized_eq_of_le (convex_convexHull ℝ _) x.property.1 hu.1 hw.1.1
        hu.2 (ha u hu) huw heq
    · exact (eq_of_normalized_eq_of_le (convex_convexHull ℝ _) x.property.1 hw.1 hu.1.1
        hw.2 (ha w hw) hwu heq.symm).symm
  have hlevels (w : E) (hw : w ∈ V) : k w ≤ k x.val ∧ (k w = k x.val ↔ w = x.val ∨ w = z) := by
    by_cases hwx : w = x.val
    · subst w
      simp
    have hw' : w ∈ V \ {x.val} := ⟨hw, hwx⟩
    by_cases hwz : w = z
    · subst w
      have heq : k z = k x.val := sub_eq_zero.1 (by simp [hk z hz, hzp])
      simp [heq]
    · have hqp : q w ≠ p := fun h => hwz (hqinj hw' hz (h.trans hzp.symm))
      have hlt : k w < k x.val := by
        rw [← sub_neg, hk w hw']
        exact mul_neg_of_pos_of_neg (ha w hw') (sub_neg.2 (hl _ (mem_image_of_mem q hw') hqp))
      simp [hlt.le, hlt.ne, hwx, hwz]
  refine ⟨⟨z, hz.1⟩, ⟨fun h => hz.2 (congrArg Subtype.val h).symm, ?_⟩,
    (hqpos z hz).1 (hzp ▸ hfp)⟩
  change IsExposed ℝ P (segment ℝ x.val z)
  rw [← hPV, ← Set.Finite.coe_toFinset hV, ← convexHull_pair]
  exact isExposed_convexHull_of_forall_le hV.toFinset {x.val, z} k (k x.val)
    (fun w hw => (hlevels w (hV.mem_toFinset.1 hw)).1)
    (by
      rintro w (rfl | hw)
      · exact ⟨hV.mem_toFinset.2 x.property, rfl⟩
      · have hwz := Set.mem_singleton_iff.1 hw
        exact hwz.symm ▸ ⟨hV.mem_toFinset.2 hz.1, (hlevels z hz.1).2.2 (Or.inr rfl)⟩)
    (fun w hw heq => (hlevels w (hV.mem_toFinset.1 hw)).2.1 heq)

/-- A small positive perturbation can break ties in favor of a chosen maximizer,
while preserving every strict comparison among the vertices. -/
private theorem exists_tilt {s : Finset E} (f : StrongDual ℝ E) (a : Vertices s)
    (ha : ∀ u : Vertices s, f u.val ≤ f a.val) :
    ∃ g : StrongDual ℝ E,
      (∀ u v : Vertices s, f u.val < f v.val → g u.val < g v.val) ∧
      (∀ u : Vertices s, u ≠ a → g u.val < g a.val) := by
  have hV := extremePoints_finite s
  let : Fintype (Vertices s) := hV.fintype
  have haV : a.val ∈ (convexHull ℝ (Vertices s)).extremePoints ℝ :=
    convexHull_vertices s.finite_toSet ▸ a.property
  obtain ⟨l, hl⟩ := exists_strict_maximizer_functional hV haV
  have hsmall (u v : Vertices s) : ∀ᶠ t in 𝓝 (0 : ℝ),
      f u.val < f v.val → f u.val + t * l u.val < f v.val + t * l v.val := by
    by_cases h : f u.val < f v.val
    · have hc (w : Vertices s) : Continuous (fun t : ℝ => f w.val + t * l w.val) := by
        fun_prop
      exact ((hc u).continuousAt.eventually_lt (hc v).continuousAt
        (by simpa using h)).mono fun _ ht _ => ht
    · exact Eventually.of_forall fun _ hh => (h hh).elim
  have hsmall' : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ u v : Vertices s,
      f u.val < f v.val → f u.val + t * l u.val < f v.val + t * l v.val :=
    eventually_all.2 fun u => eventually_all.2 (hsmall u)
  have hpos : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
  obtain ⟨t, ht, ht'⟩ := (hpos.and (eventually_nhdsWithin_of_eventually_nhds hsmall')).exists
  refine ⟨f + t • l, ht', fun u hu => ?_⟩
  rcases (ha u).lt_or_eq with hlt | heq
  · exact ht' u a hlt
  · have hla := hl u.val u.property (fun h => hu (Subtype.ext h))
    simpa only [add_apply, smul_apply, smul_eq_mul, heq, add_lt_add_iff_left] using
      mul_lt_mul_of_pos_left hla ht

/-- All vertices strictly above the level of the deleted vertices can reach the same
maximizer. A reachable vertex maximizing the perturbed objective must be that maximizer,
since any improving edge from it stays above the level. -/
private theorem reachable_above {s : Finset E} {S : Finset (Vertices s)}
    (f : StrongDual ℝ E) (c : ℝ) (hS : ∀ w ∈ S, f w.val = c)
    (x y : RemainingVertices S)
    (hx : c < f x.val.val) (hy : c < f y.val.val) :
    ((graph s).induce (S : Set (Vertices s))ᶜ).Reachable x y := by
  classical
  let : Fintype (Vertices s) := (extremePoints_finite s).fintype
  obtain ⟨a, -, ha⟩ := Finset.univ.exists_max_image (fun w : Vertices s => f w.val)
    ⟨y.val, Finset.mem_univ _⟩
  have hfa := hy.trans_le (ha _ (Finset.mem_univ _))
  let a' : RemainingVertices S :=
    ⟨a, fun h => (hS a h).not_gt hfa⟩
  obtain ⟨g, horder, hg⟩ := exists_tilt f a (fun w => ha w (Finset.mem_univ _))
  let G := (graph s).induce (S : Set (Vertices s))ᶜ
  have reach (u : RemainingVertices S) (hu : c < f u.val.val) :
      G.Reachable u a' := by
    let R := Finset.univ.filter fun w => c < f w.val.val ∧ G.Reachable u w
    have huR : u ∈ R := Finset.mem_filter.2 ⟨Finset.mem_univ _, hu, .rfl⟩
    obtain ⟨m, hm, hmmax⟩ := R.exists_max_image (fun w => g w.val.val) ⟨u, huR⟩
    obtain ⟨hfm, hreach⟩ := (Finset.mem_filter.1 hm).2
    by_cases hma : m = a'
    · exact hma ▸ hreach
    obtain ⟨z, hadj, hgz⟩ := exists_adj_gt g (hg m.val (fun h => hma (Subtype.ext h)))
    have hfz : c < f z.val := lt_of_not_ge fun h => (horder z m.val (h.trans_lt hfm)).not_gt hgz
    let z' : RemainingVertices S :=
      ⟨z, fun h => (hS z h).not_gt hfz⟩
    have hstep : G.Adj m z' := hadj
    have hzR : z' ∈ R := Finset.mem_filter.2
      ⟨Finset.mem_univ _, hfz, hreach.trans hstep.reachable⟩
    exact (hgz.not_ge (hmmax z' hzR)).elim
  exact (reach x hx).trans (reach y hy).symm

/-- A vertex on the level of the deleted vertices can first take an edge into the open
half-space, then use paths inside it. -/
private theorem reachable_to_above {s : Finset E} {S : Finset (Vertices s)}
    (f : StrongDual ℝ E) (c : ℝ) (hS : ∀ w ∈ S, f w.val = c)
    (x y : RemainingVertices S)
    (hx : c ≤ f x.val.val) (hy : c < f y.val.val) :
    ((graph s).induce (S : Set (Vertices s))ᶜ).Reachable x y := by
  rcases hx.lt_or_eq with hlt | heq
  · exact reachable_above f c hS x y hlt hy
  have hxy : f x.val.val < f y.val.val := heq ▸ hy
  obtain ⟨z, hadj, hgz⟩ := exists_adj_gt f hxy
  have hz : c < f z.val := heq.symm ▸ hgz
  let z' : RemainingVertices S :=
    ⟨z, fun h => (hS z h).not_gt hz⟩
  have hstep : ((graph s).induce (S : Set (Vertices s))ᶜ).Adj x z' := hadj
  exact hstep.reachable.trans (reachable_above f c hS z' y hz hy)

private theorem dim_eq_finrank_vectorSpan_vertices (s : Finset E) :
    dim s = Module.finrank ℝ (vectorSpan ℝ (Vertices s)) := by
  rw [← direction_affineSpan, ← affineSpan_convexHull, convexHull_vertices s.finite_toSet]
  rfl

/-- The differences from a surviving vertex to the deleted vertices span a subspace
of dimension at most the number of deletions. Some vertex difference lies outside it. -/
private theorem exists_vertex_separator [FiniteDimensional ℝ E] {s : Finset E}
    (S : Finset (Vertices s)) (hS : S.card < dim s) (b : Vertices s) :
    ∃ f : StrongDual ℝ E, (∀ v ∈ S, f v.val = f b.val) ∧ ∃ v : Vertices s, f v.val ≠ f b.val := by
  let p (v : Vertices s) := v.val - b.val
  let W := Submodule.span ℝ (p '' (S : Set (Vertices s)))
  have hW : Module.finrank ℝ W ≤ S.card := by
    refine (finrank_span_le_ncard (p '' (S : Set (Vertices s))) (S.finite_toSet.image p)).trans ?_
    exact Set.ncard_coe_finset S ▸ Set.ncard_image_le S.finite_toSet
  obtain ⟨v, hv⟩ : ∃ v : Vertices s, p v ∉ W := by
    by_contra! h
    have hVW : vectorSpan ℝ (Vertices s) ≤ W := by
      rw [vectorSpan_eq_span_vsub_set_right ℝ b.property, Submodule.span_le]
      rintro _ ⟨u, hu, rfl⟩
      exact h ⟨u, hu⟩
    exact (hW.trans_lt hS).not_ge
      (dim_eq_finrank_vectorSpan_vertices s ▸ Submodule.finrank_mono hVW)
  obtain ⟨l, hlv, hlS⟩ := Submodule.exists_le_ker_of_notMem hv
  refine ⟨l.toContinuousLinearMap, fun u hu => ?_, v, ?_⟩
  · apply sub_eq_zero.1
    simpa only [LinearMap.mem_ker, LinearMap.coe_toContinuousLinearMap', p, map_sub] using
      hlS (Submodule.subset_span (mem_image_of_mem p (Finset.mem_coe.2 hu)))
  · intro h
    apply hlv
    simp only [LinearMap.coe_toContinuousLinearMap'] at h
    simp only [p, map_sub, h, sub_self]

/-- **Balinski's theorem.** The graph of a polytope `P = conv s` of dimension `d` is
`d`-connected: it has more than `d` vertices and stays connected after deleting any fewer than
`d` vertices (M. L. Balinski, 1961; G. M. Ziegler, *Lectures on Polytopes*, GTM 152,
Theorem 3.14, as cited in Ziegler, "Convex polytopes: extremal constructions and f-vector shapes",
IAS/Park City Math. Ser. 14 (2004), Section 1.2, arXiv:math/0411400v2). The polytope must be
nonempty. -/
public theorem balinski {n d : ℕ} (s : Finset (EuclideanSpace ℝ (Fin n))) (hs : s.Nonempty)
    (hd : dim s = d) :
    @SimpleGraph.IsVertexConnected _ (extremePoints_finite s).fintype d (graph s) := by
  classical
  subst d
  let : Fintype (Vertices s) := (extremePoints_finite s).fintype
  have : Nonempty (Vertices s) := by
    obtain ⟨v, hv⟩ := (s.finite_toSet.isCompact_convexHull ℝ).extremePoints_nonempty
      (hs.to_set.convexHull)
    exact ⟨⟨v, hv⟩⟩
  have hcard : dim s < Fintype.card (Vertices s) := by
    rw [dim_eq_finrank_vectorSpan_vertices]
    apply Nat.lt_of_succ_le
    have hrange : Set.range (fun v : Vertices s => v.val) = Vertices s :=
      Subtype.range_coe_subtype
    have hsize := finrank_vectorSpan_range_add_one_le ℝ (fun v : Vertices s => v.val)
    rw [hrange] at hsize
    exact hsize
  refine ⟨hcard, fun S hS => ?_⟩
  have hlt : S.card < (Finset.univ : Finset (Vertices s)).card := by
    rw [Finset.card_univ]
    exact hS.trans hcard
  obtain ⟨b, -, hb⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  let b' : RemainingVertices S := ⟨b, hb⟩
  obtain ⟨f, hfS, v, hv⟩ := exists_vertex_separator S hS b
  have hfneg (w : Vertices s) (hw : w ∈ S) : (-f) w.val = -(f b.val) := by
    simpa only [neg_apply, neg_inj] using hfS w hw
  have hreach (y : RemainingVertices S) (hy : f y.val.val ≠ f b.val)
      (x : RemainingVertices S) (hx : f x.val.val = f b.val) :
      ((graph s).induce (S : Set (Vertices s))ᶜ).Reachable x y := by
    rcases hy.lt_or_gt with hy | hy
    · exact reachable_to_above (-f) (-(f b.val)) hfneg x y
        (by simpa using le_of_eq hx) (by simpa using hy)
    · exact reachable_to_above f (f b.val) hfS x y (le_of_eq hx.symm) hy
  -- The surviving vertex on the separating hyperplane gives access to either open side.
  refine (SimpleGraph.connected_iff_exists_forall_reachable _).2 ⟨b', fun x => ?_⟩
  by_cases hx : f x.val.val = f b.val
  · let v' : RemainingVertices S := ⟨v, fun h => hv (hfS v h)⟩
    exact (hreach v' hv b' rfl).trans (hreach v' hv x hx).symm
  · exact hreach x hx b' rfl

end MathlibExt.Geometry.Polytope.GraphWanted
