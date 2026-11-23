/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.AlgebraicTopology.SimplicialComplex.Basic
public import Mathlib.Geometry.Convex.ConvexSpace.CompactSpaceStdSimplex
public import MathlibExt.AlgebraicTopology.SimplicialSet.Subdivision.Realization
public import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.CWComplex
public import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.Subcomplex

/-!
# Weak realization of an abstract simplicial complex

The points are finitely supported nonnegative barycentric coordinates whose
support is a face. The topology is the final topology of the closed finite
face simplices. In particular it is not defined by a norm on the ambient
coordinate space. The face category consists of the actual nonempty finite
faces, ordered by inclusion.
-/

@[expose] public section

noncomputable section

open CategoryTheory Topology Opposite
open scoped Simplicial

universe u

namespace PreAbstractSimplicialComplex

variable {V : Type u}

/-- The actual nonempty finite faces, ordered by inclusion. -/
abbrev Face (P : PreAbstractSimplicialComplex V) := {s : Finset V // s ∈ P}

/-- The nerve of the partially ordered set of faces. -/
def faceNerve (P : PreAbstractSimplicialComplex V) : SSet.{u} :=
  CategoryTheory.nerve (Face P)

/-- A point of the polyhedron, before choosing its weak topology. -/
@[ext]
structure Realization (P : PreAbstractSimplicialComplex V) where
  /-- Its finite barycentric distribution. -/
  point : Convexity.StdSimplex ℝ V
  /-- Its nonzero support is an actual face. -/
  support_mem : point.weights.support ∈ P

namespace Realization

variable {P Q R : PreAbstractSimplicialComplex V}

/-- Every barycentric point in a finite face has support contained in that face. -/
theorem support_map_subtype_subset (s : Finset V)
    (q : Convexity.StdSimplex ℝ s) :
    (q.map (Subtype.val : s → V)).weights.support ⊆ s := by
  classical
  intro v hv
  by_contra hvs
  have hvr : v ∉ Set.range (Subtype.val : s → V) := by
    rintro ⟨w, rfl⟩
    exact hvs w.property
  have hz : (q.map (Subtype.val : s → V)).weights v = 0 := by
    rw [Convexity.StdSimplex.weights_map]
    exact Finsupp.mapDomain_of_notMem_range _ _ hvr
  exact (Finsupp.mem_support_iff.mp hv) hz

/-- The closed simplex of a face maps to the polyhedron by its literal
barycentric coordinates. -/
def faceMap (P : PreAbstractSimplicialComplex V) (s : Face P)
    (q : Convexity.StdSimplex ℝ s.val) : Realization P where
  point := q.map (Subtype.val : s.val → V)
  support_mem := (P.isRelLowerSet_faces s.property).2
    (support_map_subtype_subset s.val q)
    (q.map (Subtype.val : s.val → V)).support_weights_nonempty

/-- The weak topology is the supremum of the coinduced finite-face topologies. -/
@[instance_reducible]
def weakTopology (P : PreAbstractSimplicialComplex V) : TopologicalSpace (Realization P) :=
  ⨆ s : Face P, TopologicalSpace.coinduced (faceMap P s) inferInstance

instance (P : PreAbstractSimplicialComplex V) : TopologicalSpace (Realization P) := weakTopology P

/-- A map from the weak polyhedron is continuous exactly when it is
continuous on every closed finite face. -/
theorem continuous_iff {X : Type*} [TopologicalSpace X] (f : Realization P → X) :
    Continuous f ↔ ∀ s : Face P, Continuous (f ∘ faceMap P s) := by
  change Continuous[⨆ s : Face P,
    TopologicalSpace.coinduced (faceMap P s) inferInstance, _] f ↔ _
  simp only [continuous_iSup_dom, continuous_coinduced_dom]

/-- The closed-set form of the weak topology. -/
theorem isClosed_iff (A : Set (Realization P)) :
    IsClosed A ↔ ∀ s : Face P, IsClosed ((faceMap P s) ⁻¹' A) := by
  change IsClosed[⨆ s : Face P,
    TopologicalSpace.coinduced (faceMap P s) inferInstance] A ↔ _
  simp only [isClosed_iSup_iff, isClosed_coinduced]

@[fun_prop]
theorem continuous_faceMap (P : PreAbstractSimplicialComplex V) (s : Face P) :
    Continuous (faceMap P s) := by
  rw [continuous_iff_coinduced_le]
  exact le_iSup (fun s : Face P =>
    TopologicalSpace.coinduced (faceMap P s) inferInstance) s

@[fun_prop]
theorem continuous_point (P : PreAbstractSimplicialComplex V) :
    Continuous (point : Realization P → Convexity.StdSimplex ℝ V) := by
  rw [continuous_iff]
  intro s
  exact Convexity.StdSimplex.continuous_map ℝ (Subtype.val : s.val → V)

@[fun_prop]
theorem continuous_weight (P : PreAbstractSimplicialComplex V) (v : V) :
    Continuous (fun x : Realization P => x.point.weights v) :=
  (Convexity.StdSimplex.continuous_weights_apply ℝ v).comp (continuous_point P)

instance (P : PreAbstractSimplicialComplex V) : T2Space (Realization P) :=
  T2Space.of_injective_continuous
    (f := fun x : Realization P => (x.point.weights : V → ℝ))
    (fun {x y} h => by
      have hw : x.point.weights = y.point.weights := Finsupp.ext (congr_fun h)
      exact Realization.ext (Convexity.StdSimplex.weights_inj.mp hw))
    (continuous_pi (continuous_weight P))

/-- Each finite closed face is genuinely embedded in the weak realization. -/
theorem isClosedEmbedding_faceMap (P : PreAbstractSimplicialComplex V) (s : Face P) :
    IsClosedEmbedding (faceMap P s) :=
  (continuous_faceMap P s).isClosedEmbedding (by
    intro a b h
    exact Convexity.StdSimplex.map_injective Subtype.val_injective
      (congrArg point h))

/-- Membership in a face image is exactly containment of the barycentric support. -/
theorem mem_range_faceMap_iff (s : Face P) (x : Realization P) :
    x ∈ Set.range (faceMap P s) ↔ x.point.weights.support ⊆ s.val := by
  classical
  constructor
  · rintro ⟨q, rfl⟩
    exact support_map_subtype_subset s.val q
  · intro hx
    have hq : x.point ∈ Set.range (Convexity.StdSimplex.map (Subtype.val : s.val → V)) := by
      rw [Convexity.StdSimplex.mem_range_map_iff]
      intro v hv
      by_contra hz
      exact hv ⟨⟨v, hx (Finsupp.mem_support_iff.mpr hz)⟩, rfl⟩
    obtain ⟨q, hq⟩ := hq
    exact ⟨q, Realization.ext hq⟩

/-- Every point lies in the closed face given by its own nonzero support. -/
theorem mem_range_support_face (x : Realization P) :
    x ∈ Set.range (faceMap P ⟨x.point.weights.support, x.support_mem⟩) :=
  (mem_range_faceMap_iff _ x).mpr (Finset.Subset.refl _)

/-- The actual inclusion of one subcomplex in another. -/
def inclusion (h : P ≤ Q) (x : Realization P) : Realization Q :=
  ⟨x.point, h x.support_mem⟩

@[simp]
theorem inclusion_point (h : P ≤ Q) (x : Realization P) :
    (inclusion h x).point = x.point := rfl

@[simp]
theorem inclusion_faceMap (h : P ≤ Q) (s : Face P)
    (q : Convexity.StdSimplex ℝ s.val) :
    inclusion h (faceMap P s q) = faceMap Q ⟨s.val, h s.property⟩ q := rfl

@[fun_prop]
theorem continuous_inclusion (h : P ≤ Q) : Continuous (inclusion h) := by
  rw [continuous_iff]
  intro s
  exact continuous_faceMap Q ⟨s.val, h s.property⟩

theorem inclusion_injective (h : P ≤ Q) : Function.Injective (inclusion h) :=
  fun _ _ hxy => Realization.ext (congrArg (point (P := Q)) hxy)

/-- A closed subset of a subcomplex stays closed in the larger weak polyhedron.
On any finite face it is a finite union of compact closed face pieces. -/
theorem isClosed_inclusion_image (h : P ≤ Q) {A : Set (Realization P)} (hA : IsClosed A) :
    IsClosed (inclusion h '' A) := by
  classical
  rw [isClosed_iff]
  intro s
  let J := {t : Finset V // t ∈ P ∧ t ⊆ s.val}
  have : Finite J := Finite.of_injective
    (fun t : J => (⟨t.val, Finset.mem_powerset.mpr t.property.2⟩ : s.val.powerset))
    (by intro a b hab; exact Subtype.ext (congrArg (fun z : s.val.powerset => z.val) hab))
  let B (t : J) : Set (Realization Q) :=
    (fun q => inclusion h (faceMap P ⟨t.val, t.property.1⟩ q)) ''
      ((faceMap P ⟨t.val, t.property.1⟩) ⁻¹' A)
  have hB (t : J) : IsClosed (B t) :=
    ((hA.preimage (continuous_faceMap P ⟨t.val, t.property.1⟩)).isCompact.image
      ((continuous_inclusion h).comp (continuous_faceMap P ⟨t.val, t.property.1⟩))).isClosed
  have heq : (faceMap Q s) ⁻¹' (inclusion h '' A) =
      (faceMap Q s) ⁻¹' (⋃ t : J, B t) := by
    ext q
    simp only [Set.mem_preimage, Set.mem_image, Set.mem_iUnion]
    constructor
    · rintro ⟨x, hxA, hxq⟩
      have hs := (mem_range_faceMap_iff s (inclusion h x)).mp ⟨q, hxq.symm⟩
      let t : J := ⟨x.point.weights.support, x.support_mem, hs⟩
      obtain ⟨p, hp⟩ := mem_range_support_face x
      refine ⟨t, p, ?_, ?_⟩
      · change faceMap P ⟨x.point.weights.support, x.support_mem⟩ p ∈ A
        rw [hp]
        exact hxA
      · change inclusion h (faceMap P ⟨x.point.weights.support, x.support_mem⟩ p) = _
        rw [hp]
        exact hxq
    · rintro ⟨t, p, hp, hpq⟩
      exact ⟨faceMap P ⟨t.val, t.property.1⟩ p, hp, hpq⟩
  rw [heq]
  exact (isClosed_iUnion_of_finite hB).preimage (continuous_faceMap Q s)

/-- Every actual abstract subcomplex inclusion is a closed topological embedding. -/
theorem isClosedEmbedding_inclusion (h : P ≤ Q) : IsClosedEmbedding (inclusion h) :=
  .of_continuous_injective_isClosedMap (continuous_inclusion h) (inclusion_injective h)
    (fun _ hA => isClosed_inclusion_image h hA)

/-- The image of a subcomplex consists exactly of the points whose support is one of its faces. -/
theorem mem_range_inclusion_iff (h : P ≤ Q) (x : Realization Q) :
    x ∈ Set.range (inclusion h) ↔ x.point.weights.support ∈ P := by
  constructor
  · rintro ⟨y, rfl⟩
    exact y.support_mem
  · intro hx
    exact ⟨⟨x.point, hx⟩, rfl⟩

@[simp]
theorem inclusion_refl (x : Realization P) : inclusion le_rfl x = x := rfl

@[simp]
theorem inclusion_trans (h : P ≤ Q) (k : Q ≤ R) (x : Realization P) :
    inclusion k (inclusion h x) = inclusion (h.trans k) x := rfl

/-- A literal barycentric vertex, with its actual singleton-face certificate. -/
def vertex (P : PreAbstractSimplicialComplex V) (v : V) (hv : {v} ∈ P) :
    Realization P where
  point := Convexity.StdSimplex.single v
  support_mem := by simpa using hv

section FiniteFaceQuotient

variable (P : PreAbstractSimplicialComplex V)

/-- The actual finite-face sigma map defining the original weak topology. -/
def faceSigmaMap : (Σ s : Face P, Convexity.StdSimplex ℝ s.val) → Realization P :=
  fun q => faceMap P q.1 q.2

private theorem continuous_faceSigmaMap_computed : Continuous (faceSigmaMap P) :=
  continuous_sigma_iff.mpr (continuous_faceMap P)

/-- The original weak realization is the quotient of all its actual finite faces. -/
theorem isQuotientMap_faceSigmaMap : IsQuotientMap (faceSigmaMap P) := by
  refine ⟨Topology.isCoinducing_iff.mpr ?_, ?_⟩
  · intro S
    constructor
    · intro hS
      have hTest : Continuous (fun q => faceSigmaMap P q ∈ S) := continuous_Prop.mpr hS
      have hFaces := continuous_sigma_iff.mp hTest
      have hWeak : Continuous (fun x : Realization P => x ∈ S) :=
        (continuous_iff _).mpr hFaces
      exact continuous_Prop.mp hWeak
    · intro hS
      exact hS.preimage (continuous_faceSigmaMap_computed P)
  · intro x
    obtain ⟨q, hq⟩ := mem_range_support_face x
    exact ⟨⟨⟨x.point.weights.support, x.support_mem⟩, q⟩, hq⟩

end FiniteFaceQuotient

end Realization

/-- Inclusion of actual faces along an abstract subcomplex inclusion. -/
def faceInclusion {P Q : PreAbstractSimplicialComplex V} (h : P ≤ Q) : Face P →o Face Q where
  toFun s := ⟨s.val, h s.property⟩
  monotone' := fun _ _ hst => hst

/-- The corresponding actual face-poset nerve map. -/
def faceNerveInclusion {P Q : PreAbstractSimplicialComplex V} (h : P ≤ Q) :
    faceNerve P ⟶ faceNerve Q :=
  CategoryTheory.nerveMap (faceInclusion h).monotone.functor

instance {P Q : PreAbstractSimplicialComplex V} (h : P ≤ Q) : Mono (faceNerveInclusion h) := by
  rw [NatTrans.mono_iff_mono_app]
  intro n
  rw [mono_iff_injective]
  intro a b hab
  apply ComposableArrows.ext (F := a) (G := b)
    (h := fun j => Subtype.ext (congrArg (fun z : (faceNerve Q).obj n => (z.obj j).val) hab))
    (w := by intro j hj; subsingleton)

/-- The actual face-poset realization also embeds subcomplexes as closed subspaces. -/
theorem isClosedEmbedding_toTop_faceNerveInclusion
    {P Q : PreAbstractSimplicialComplex V} (h : P ≤ Q) :
    IsClosedEmbedding (SSet.toTop.map (faceNerveInclusion h)).hom :=
  TopCat.closedT1Embeddings_le_isClosedEmbedding _
    (SSet.closedT1Embeddings_toTop_map_of_mono (faceNerveInclusion h))

/-- The specified vertex is represented by its literal singleton face in the nerve. -/
def faceNerveVertex (P : PreAbstractSimplicialComplex V) (v : V) (hv : {v} ∈ P) :
    (faceNerve P) _⦋0⦌ :=
  CategoryTheory.nerveEquiv.symm ⟨{v}, hv⟩

/-- This literal singleton-face nerve vertex is an actual classical zero cell. -/
theorem realizedFaceNerveVertex_is_classical_zeroCell
    (P : PreAbstractSimplicialComplex V) (v : V) (hv : {v} ∈ P) :
    ∃ j : Topology.CWComplex.cell (Set.univ : Set (SSet.toTop.obj (faceNerve P))) 0,
      ∀ x : Fin 0 → ℝ, Topology.CWComplex.map 0 j x =
        SSet.realizedVertex (faceNerveVertex P v hv) :=
  SSet.realizedVertex_is_classical_zeroCell _

section FiniteSimplex

variable {W : Type u} {n : ℕ}

open Classical in
/-- Nonempty coordinate subsets of a finite simplex are exactly its abstract faces.
The arbitrary enumeration is used only to identify this one finite simplex. -/
def finiteSimplexFaceOrderIso (e : Fin (n + 1) ≃ W) :
    PartialOrder.NonemptyFiniteChains (ULift.{u} (Fin (n + 1))) ≃o
      Face (⊤ : PreAbstractSimplicialComplex W) where
  toFun c := ⟨c.finset.image (fun j => e j.down), c.nonempty.image _⟩
  invFun s :=
    { finset := s.val.image (fun w => ULift.up (e.symm w))
      nonempty := s.property.image _
      comparable a b := le_total a b }
  left_inv c := by
    apply PartialOrder.NonemptyFiniteChains.ext
    change (c.finset.image (fun j => e j.down)).image
      (fun w => ULift.up (e.symm w)) = c.finset
    rw [Finset.image_image]
    have h : ((fun w => ULift.up (e.symm w)) ∘ fun j => e j.down) = id := by
      funext j
      simp
    rw [h, Finset.image_id]
  right_inv s := by
    apply Subtype.ext
    change (s.val.image (fun w => ULift.up (e.symm w))).image
      (fun j => e j.down) = s.val
    rw [Finset.image_image]
    have h : ((fun j => e j.down) ∘ fun w => ULift.up (e.symm w)) = id := by
      funext w
      simp
    rw [h, Finset.image_id]
  map_rel_iff' := by
    intro a b
    change a.finset.image (fun j => e j.down) ⊆ b.finset.image (fun j => e j.down) ↔
      a.finset ⊆ b.finset
    exact Finset.image_subset_image_iff (e.injective.comp ULift.down_injective)

/-- The finite face-poset nerve is literally the categorical subdivision of a simplex. -/
def finiteSimplexFaceNerveIso (e : Fin (n + 1) ≃ W) :
    SimplexCategory.sd.{u}.obj ⦋n⦌ ≅ faceNerve (⊤ : PreAbstractSimplicialComplex W) :=
  PartOrd.nerveFunctor.mapIso (PartOrd.Iso.mk
    (α := PartOrd.of (PartialOrder.NonemptyFiniteChains (ULift.{u} (Fin (n + 1)))))
    (β := PartOrd.of (Face (⊤ : PreAbstractSimplicialComplex W)))
    (finiteSimplexFaceOrderIso e))

/-- Relabeling finite barycentric coordinates preserves their actual topology. -/
def simplexRelabelHomeomorph {X Y : Type*} (e : X ≃ Y) :
    Convexity.StdSimplex ℝ X ≃ₜ Convexity.StdSimplex ℝ Y where
  toFun := Convexity.StdSimplex.map e
  invFun := Convexity.StdSimplex.map e.symm
  left_inv q := by
    rw [← Convexity.StdSimplex.map_comp, Equiv.symm_comp_self]
    exact Convexity.StdSimplex.map_id q
  right_inv q := by
    rw [← Convexity.StdSimplex.map_comp, Equiv.self_comp_symm]
    exact Convexity.StdSimplex.map_id q
  continuous_toFun := Convexity.StdSimplex.continuous_map ℝ e
  continuous_invFun := Convexity.StdSimplex.continuous_map ℝ e.symm

/-- The actual finite face-poset realization is homeomorphic to the standard
simplex on the same vertices. It uses the proved affine subdivision homeomorphism. -/
def finiteSimplexFaceHomeomorph (e : Fin (n + 1) ≃ W) :
    SSet.toTop.obj (faceNerve (⊤ : PreAbstractSimplicialComplex W)) ≃ₜ
      Convexity.StdSimplex ℝ W :=
  (TopCat.homeoOfIso
    ((SSet.toTop.mapIso (finiteSimplexFaceNerveIso e)).symm ≪≫
      (SSet.toTop.mapIso (SSet.stdSimplex.sdIso.{u}.app ⦋n⦌)).symm ≪≫
        SSet.toTopSdIso (SSet.stdSimplex.obj ⦋n⦌))).trans
    ((SimplexCategory.toTopHomeo.{u} ⦋n⦌).trans (simplexRelabelHomeomorph e))

end FiniteSimplex

namespace Realization

variable {P : PreAbstractSimplicialComplex V}

/-- The affine barycentric point of a chain of actual finite faces. -/
def chainPoint {n : ℕ} (σ : (faceNerve P) _⦋n⦌)
    (q : Convexity.StdSimplex ℝ (Fin (n + 1))) : Convexity.StdSimplex ℝ V :=
  q.iConvexComb (fun j => Convexity.StdSimplex.subBarycenter
    (σ.obj j).val (P.isRelLowerSet_faces (σ.obj j).property).1)

/-- The affine chain point is supported in its final face. -/
theorem chainPoint_support_subset {n : ℕ} (σ : (faceNerve P) _⦋n⦌)
    (q : Convexity.StdSimplex ℝ (Fin (n + 1))) :
    (chainPoint σ q).weights.support ⊆ (σ.obj (Fin.last n)).val := by
  classical
  intro v hv
  by_contra hvs
  have hzero (j : Fin (n + 1)) :
      (Convexity.StdSimplex.subBarycenter (K := ℝ)
        (σ.obj j).val (P.isRelLowerSet_faces (σ.obj j).property).1).weights v = 0 :=
    Convexity.StdSimplex.subBarycenter_weights_apply_eq_zero _ _ _
      (fun hvj => hvs (σ.monotone (Fin.le_last j) hvj))
  have hz : (chainPoint σ q).weights v = 0 := by
    simp only [chainPoint, Convexity.StdSimplex.weights_iConvexComb_apply, hzero,
      mul_zero, Finset.sum_const_zero]
  exact (Finsupp.mem_support_iff.mp hv) hz

/-- The affine map on a chain cell, valued in the actual weak polyhedron. -/
def chainMap (P : PreAbstractSimplicialComplex V) {n : ℕ}
    (σ : (faceNerve P) _⦋n⦌) (q : Convexity.StdSimplex ℝ (Fin (n + 1))) :
    Realization P where
  point := chainPoint σ q
  support_mem := (P.isRelLowerSet_faces (σ.obj (Fin.last n)).property).2
    (chainPoint_support_subset σ q) (chainPoint σ q).support_weights_nonempty

/-- Finite affine mixtures into a finite simplex are continuous in their actual topology. -/
theorem continuous_finite_mixture {J W : Type*} [Finite J] [Finite W]
    (b : J → Convexity.StdSimplex ℝ W) :
    Continuous (fun q : Convexity.StdSimplex ℝ J => q.iConvexComb b) := by
  let := Fintype.ofFinite J
  apply (Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ W).continuous_iff.mpr
  apply continuous_pi
  intro w
  simp only [Function.comp_apply, Convexity.StdSimplex.weights_iConvexComb_apply]
  exact continuous_finsetSum _ (fun j _ =>
    (Convexity.StdSimplex.continuous_weights_apply ℝ j).mul continuous_const)

/-- Each affine chain cell is continuous for the weak finite-face topology. -/
@[fun_prop]
theorem continuous_chainMap (P : PreAbstractSimplicialComplex V) {n : ℕ}
    (σ : (faceNerve P) _⦋n⦌) : Continuous (chainMap P σ) := by
  let t := σ.obj (Fin.last n)
  have hb (j : Fin (n + 1)) : chainMap P σ (Convexity.StdSimplex.single j) ∈
      Set.range (faceMap P t) :=
    (mem_range_faceMap_iff t _).mpr (chainPoint_support_subset σ _)
  choose b hb using hb
  have heq : chainMap P σ =
      faceMap P t ∘ (fun q => q.iConvexComb b) := by
    funext q
    apply Realization.ext
    change chainPoint σ q = (q.iConvexComb b).map (Subtype.val : t.val → V)
    rw [Convexity.map_iConvexComb]
    apply Convexity.iConvexComb_congr
    intro j _
    have hj := congrArg (point (P := P)) (hb j)
    simpa [chainMap, chainPoint, faceMap] using hj.symm
  rw [heq]
  exact (continuous_faceMap P t).comp (continuous_finite_mixture b)

/-- All simplex face and degeneracy operators preserve the affine chain map. -/
theorem chainMap_restrict {m n : ℕ} (f : ⦋m⦌ ⟶ ⦋n⦌)
    (σ : (faceNerve P) _⦋n⦌) (q : Convexity.StdSimplex ℝ (Fin (m + 1))) :
    chainMap P ((faceNerve P).map f.op σ) q = chainMap P σ (q.map f) := by
  apply Realization.ext
  change q.iConvexComb _ = (q.map f).iConvexComb _
  rw [Convexity.iConvexComb_map]
  rfl

/-- The actual affine chain maps give a simplicial map into the singular complex. -/
def affineSingularMap (P : PreAbstractSimplicialComplex V) :
    faceNerve P ⟶ TopCat.toSSet.obj (TopCat.of (Realization P)) where
  app d := ↾fun σ =>
    (TopCat.toSSetObjEquiv (TopCat.of (Realization P)) d).symm
      ⟨chainMap P σ, continuous_chainMap P σ⟩
  naturality d e f := by
    obtain ⟨d, rfl⟩ : ∃ k, op (SimplexCategory.mk k) = d :=
      ⟨d.unop.len, congrArg op d.unop.mk_len⟩
    obtain ⟨e, rfl⟩ : ∃ k, op (SimplexCategory.mk k) = e :=
      ⟨e.unop.len, congrArg op e.unop.mk_len⟩
    ext σ
    apply (TopCat.toSSetObjEquiv (TopCat.of (Realization P)) (op (SimplexCategory.mk e))).injective
    apply ContinuousMap.ext
    intro q
    exact chainMap_restrict f.unop σ q

/-- The concrete affine map from the face-poset nerve realization to the weak polyhedron. -/
def affineToTop (P : PreAbstractSimplicialComplex V) :
    SSet.toTop.obj (faceNerve P) ⟶ TopCat.of (Realization P) :=
  (sSetTopAdj.homEquiv _ _).symm (affineSingularMap P)

/-- On every actual nerve cell the global affine map is the specified barycentric mixture. -/
theorem affineToTop_cell (P : PreAbstractSimplicialComplex V) {n : ℕ}
    (σ : (faceNerve P) _⦋n⦌) (q : Convexity.StdSimplex ℝ (Fin (n + 1))) :
    affineToTop P (SSet.toTop.map (SSet.yonedaEquiv.symm σ)
      ((SimplexCategory.toTopHomeo.{u} ⦋n⦌).symm q)) = chainMap P σ q := by
  have hAdj := (sSetTopAdj.homEquiv (faceNerve P)
    (TopCat.of (Realization P))).apply_symm_apply (affineSingularMap P)
  rw [Adjunction.homEquiv_unit] at hAdj
  have hDown := congrArg (fun r => (r.app _ σ).down) hAdj
  change ((sSetTopAdj.unit.app (faceNerve P)).app _ σ).down ≫ affineToTop P =
    ((affineSingularMap P).app _ σ).down at hDown
  rw [sSetTopAdj_unit_app_app_down] at hDown
  exact ConcreteCategory.congr_hom hDown (ULift.up q)

open Classical in
/-- An injective relabeling carries the uniform barycenter to the uniform
barycenter of its image, with the actual finite cardinal unchanged. -/
theorem map_subBarycenter_injective {X Y : Type*} (f : X → Y)
    (hf : Function.Injective f) (s : Finset X) (hs : s.Nonempty) :
    (Convexity.StdSimplex.subBarycenter (K := ℝ) s hs).map f =
      Convexity.StdSimplex.subBarycenter (s.image f) (hs.image f) := by
  classical
  apply Convexity.StdSimplex.ext
  simp only [Convexity.StdSimplex.weights_map, Convexity.StdSimplex.weights_subBarycenter,
    Finsupp.mapDomain_finsetSum, Finsupp.mapDomain_single,
    Finset.card_image_of_injective s hf]
  rw [Finset.sum_image]
  intro x hx y hy hxy
  exact hf hxy

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The finite face-poset identification has the same affine barycentric formula
as the proved categorical subdivision charts. -/
theorem chainPoint_finiteSimplexFaceNerveIso {W : Type u} {n d : ℕ}
    (e : Fin (n + 1) ≃ W) (σ : (SimplexCategory.sd.{u}.obj ⦋n⦌) _⦋d⦌)
    (q : Convexity.StdSimplex ℝ (Fin (d + 1))) :
    chainPoint ((finiteSimplexFaceNerveIso e).hom.app _ σ) q =
      (SimplexCategory.sdCellMap σ q).map e := by
  classical
  have hcell : SimplexCategory.sdCellMap σ q =
      q.iConvexComb (fun j => Convexity.StdSimplex.subBarycenter (K := ℝ)
        ((σ.obj j).finset.image (fun i => (i.down : Fin (n + 1))))
        ((σ.obj j).nonempty.image _)) := by
    apply Convexity.StdSimplex.ext
    apply Finsupp.ext
    intro i
    rw [SimplexCategory.sdCellMap_weights_apply,
      Convexity.StdSimplex.weights_iConvexComb_apply]
  rw [hcell, Convexity.map_iConvexComb]
  apply Convexity.iConvexComb_congr
  intro j _
  dsimp [finiteSimplexFaceNerveIso, PartOrd.nerveFunctor, CategoryTheory.nerveMap,
    CategoryTheory.Functor.mapComposableArrows, finiteSimplexFaceOrderIso]
  rw [map_subBarycenter_injective e e.injective]
  congr 1
  rw [Finset.image_image]
  ext w
  simp only [Finset.mem_image, Function.comp_apply]

/-- The standard-simplex case of the public subdivision cell formula. -/
theorem toTopSdIso_stdSimplex_cell {n d : ℕ}
    (σ : (SimplexCategory.sd.{u}.obj ⦋n⦌) _⦋d⦌)
    (q : Convexity.StdSimplex ℝ (Fin (d + 1))) :
    (SSet.toTopSdIso (SSet.stdSimplex.obj ⦋n⦌)).hom
      (SSet.toTop.map (SSet.yonedaEquiv.symm
        ((SSet.stdSimplex.sdIso.inv.app ⦋n⦌).app _ σ))
        ((SimplexCategory.toTopHomeo.{u} ⦋d⦌).symm q)) =
    (SimplexCategory.toTopHomeo.{u} ⦋n⦌).symm (SimplexCategory.sdCellMap σ q) := by
  let x : (SSet.stdSimplex.obj ⦋n⦌ : SSet.{u}).N :=
    SSet.N.mk (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋n⦌))
      (SSet.stdSimplex.objEquiv_symm_id_mem_nonDegenerate n)
  have h := SSet.toTopSdIso_hom_cell_apply (SSet.stdSimplex.obj ⦋n⦌) x σ q
  change (SSet.toTopSdIso (SSet.stdSimplex.obj ⦋n⦌)).hom
    (SSet.toTop.map (SSet.sd.map (SSet.yonedaEquiv.symm
      (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋n⦌))))
      (SSet.toTop.map (SSet.yonedaEquiv.symm
        ((SSet.stdSimplex.sdIso.inv.app ⦋n⦌).app _ σ))
        ((SimplexCategory.toTopHomeo.{u} ⦋d⦌).symm q))) =
    SSet.toTop.map (SSet.yonedaEquiv.symm
      (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋n⦌)))
      ((SimplexCategory.toTopHomeo.{u} ⦋n⦌).symm (SimplexCategory.sdCellMap σ q)) at h
  rw [SSet.yonedaEquiv_symm_stdSimplex_id, SSet.sd.map_id, SSet.toTop.map_id] at h
  simpa only [SSet.toTop.map_id, TopCat.id_app] using h

/-- Actual cell presentations commute with a simplicial map. -/
theorem realizedCell_naturality {X Y : SSet.{u}} (f : X ⟶ Y) {n : ℕ}
    (σ : X _⦋n⦌) (q : Convexity.StdSimplex ℝ (Fin (n + 1))) :
    SSet.toTop.map f (SSet.toTop.map (SSet.yonedaEquiv.symm σ)
      ((SimplexCategory.toTopHomeo.{u} ⦋n⦌).symm q)) =
    SSet.toTop.map (SSet.yonedaEquiv.symm (f.app _ σ))
      ((SimplexCategory.toTopHomeo.{u} ⦋n⦌).symm q) := by
  change (SSet.toTop.map (SSet.yonedaEquiv.symm σ) ≫ SSet.toTop.map f)
    ((SimplexCategory.toTopHomeo.{u} ⦋n⦌).symm q) = _
  rw [← SSet.toTop.map_comp, SSet.yonedaEquiv_symm_comp]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The finite face-poset homeomorphism is literally the affine barycentric map on cells. -/
theorem finiteSimplexFaceHomeomorph_cell {W : Type u} {n d : ℕ}
    (e : Fin (n + 1) ≃ W) (σ : (SimplexCategory.sd.{u}.obj ⦋n⦌) _⦋d⦌)
    (q : Convexity.StdSimplex ℝ (Fin (d + 1))) :
    finiteSimplexFaceHomeomorph e
      (SSet.toTop.map (SSet.yonedaEquiv.symm ((finiteSimplexFaceNerveIso e).hom.app _ σ))
        ((SimplexCategory.toTopHomeo.{u} ⦋d⦌).symm q)) =
    (SimplexCategory.sdCellMap σ q).map e := by
  have hinv : SSet.toTop.map (finiteSimplexFaceNerveIso e).inv
      (SSet.toTop.map (SSet.yonedaEquiv.symm ((finiteSimplexFaceNerveIso e).hom.app _ σ))
        ((SimplexCategory.toTopHomeo.{u} ⦋d⦌).symm q)) =
      SSet.toTop.map (SSet.yonedaEquiv.symm σ)
        ((SimplexCategory.toTopHomeo.{u} ⦋d⦌).symm q) := by
    rw [realizedCell_naturality]
    have hσ : (finiteSimplexFaceNerveIso e).inv.app _
        ((finiteSimplexFaceNerveIso e).hom.app _ σ) = σ :=
      congrArg (fun f => f.app _ σ) (Iso.hom_inv_id (finiteSimplexFaceNerveIso e))
    rw [hσ]
  change (SimplexCategory.toTopHomeo.{u} ⦋n⦌
    ((SSet.toTopSdIso (SSet.stdSimplex.obj ⦋n⦌)).hom
      (SSet.toTop.map (SSet.stdSimplex.sdIso.{u}.app ⦋n⦌).inv
        (SSet.toTop.map (finiteSimplexFaceNerveIso e).inv
          (SSet.toTop.map
            (SSet.yonedaEquiv.symm ((finiteSimplexFaceNerveIso e).hom.app _ σ))
            ((SimplexCategory.toTopHomeo.{u} ⦋d⦌).symm q)))))).map e = _
  rw [hinv, realizedCell_naturality, Iso.app_inv, toTopSdIso_stdSimplex_cell,
    Homeomorph.apply_symm_apply]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- On the entire finite face-poset realization the concrete homeomorphism
agrees with the global affine map, not only with an abstract comparison. -/
theorem finiteSimplexFaceHomeomorph_eq_affineToTop {W : Type u} {n : ℕ}
    (e : Fin (n + 1) ≃ W)
    (z : SSet.toTop.obj (faceNerve (⊤ : PreAbstractSimplicialComplex W))) :
    finiteSimplexFaceHomeomorph e z =
      (affineToTop (⊤ : PreAbstractSimplicialComplex W) z).point := by
  obtain ⟨y, rfl⟩ := (TopCat.homeoOfIso (SSet.toTop.mapIso
    (finiteSimplexFaceNerveIso e))).surjective z
  obtain ⟨d, σ, _, q, _, rfl⟩ := SSet.exists_nonDegenerate_interior_presentation
    (SimplexCategory.sd.{u}.obj ⦋n⦌) y
  change finiteSimplexFaceHomeomorph e
    (SSet.toTop.map (finiteSimplexFaceNerveIso e).hom
      (SSet.toTop.map (SSet.yonedaEquiv.symm σ)
        ((SimplexCategory.toTopHomeo.{u} ⦋d⦌).symm q))) =
    (affineToTop (⊤ : PreAbstractSimplicialComplex W)
      (SSet.toTop.map (finiteSimplexFaceNerveIso e).hom
        (SSet.toTop.map (SSet.yonedaEquiv.symm σ)
          ((SimplexCategory.toTopHomeo.{u} ⦋d⦌).symm q)))).point
  rw [realizedCell_naturality, finiteSimplexFaceHomeomorph_cell, affineToTop_cell]
  exact (chainPoint_finiteSimplexFaceNerveIso e σ q).symm

/-- Include all nonempty subfaces of one actual face in the whole face poset. -/
def finiteFaceOrderMap (P : PreAbstractSimplicialComplex V) (s : Face P) :
    Face (⊤ : PreAbstractSimplicialComplex s.val) →o Face P := by
  classical
  exact
    { toFun := fun t =>
        ⟨t.val.image (Subtype.val : s.val → V),
          (P.isRelLowerSet_faces s.property).2
            (by rintro v hv; obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hv; exact w.property)
            (t.property.image _)⟩
      monotone' := fun _ _ h => Finset.image_mono (Subtype.val : s.val → V) h }

/-- The actual nerve map of the finite closed-face poset. -/
def finiteFaceNerveMap (P : PreAbstractSimplicialComplex V) (s : Face P) :
    faceNerve (⊤ : PreAbstractSimplicialComplex s.val) ⟶ faceNerve P :=
  CategoryTheory.nerveMap (finiteFaceOrderMap P s).monotone.functor

/-- An enumeration of the actual vertices of a nonempty finite face. -/
def faceEnumeration (s : Face P) : Fin (s.val.card - 1 + 1) ≃ s.val :=
  (Finset.equivFinOfCardEq (s := s.val) (by
    have hcard := Finset.card_pos.mpr (P.isRelLowerSet_faces s.property).1
    omega)).symm

/-- The concrete affine homeomorphism on a particular finite closed face. -/
def finiteFaceHomeomorph (P : PreAbstractSimplicialComplex V) (s : Face P) :
    SSet.toTop.obj (faceNerve (⊤ : PreAbstractSimplicialComplex s.val)) ≃ₜ
      Convexity.StdSimplex ℝ s.val :=
  finiteSimplexFaceHomeomorph (faceEnumeration s)

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The actual finite-face chart commutes with the global affine map. -/
theorem affineToTop_finiteFaceMap (P : PreAbstractSimplicialComplex V) (s : Face P)
    (z : SSet.toTop.obj (faceNerve (⊤ : PreAbstractSimplicialComplex s.val))) :
    affineToTop P (SSet.toTop.map (finiteFaceNerveMap P s) z) =
      faceMap P s (finiteFaceHomeomorph P s z) := by
  obtain ⟨d, σ, _, q, _, rfl⟩ := SSet.exists_nonDegenerate_interior_presentation
    (faceNerve (⊤ : PreAbstractSimplicialComplex s.val)) z
  rw [realizedCell_naturality, affineToTop_cell]
  change chainMap P ((finiteFaceNerveMap P s).app _ σ) q =
    faceMap P s (finiteSimplexFaceHomeomorph (faceEnumeration s)
      (SSet.toTop.map (SSet.yonedaEquiv.symm σ)
        ((SimplexCategory.toTopHomeo.{u} ⦋d⦌).symm q)))
  rw [finiteSimplexFaceHomeomorph_eq_affineToTop, affineToTop_cell]
  apply Realization.ext
  change chainPoint ((finiteFaceNerveMap P s).app _ σ) q =
    (chainPoint σ q).map (Subtype.val : s.val → V)
  unfold chainPoint
  rw [Convexity.map_iConvexComb]
  apply Convexity.iConvexComb_congr
  intro j _
  dsimp [finiteFaceNerveMap, finiteFaceOrderMap, CategoryTheory.nerveMap,
    CategoryTheory.Functor.mapComposableArrows]
  exact (map_subBarycenter_injective (Subtype.val : s.val → V) Subtype.val_injective
    (σ.obj j).val (σ.obj j).property).symm

/-- The coefficient of a vertex in the uniform barycenter of a face. -/
theorem subBarycenter_weight_of_mem (s : Finset V) (hs : s.Nonempty) {v : V} (hv : v ∈ s) :
    (Convexity.StdSimplex.subBarycenter (K := ℝ) s hs).weights v = (s.card : ℝ)⁻¹ := by
  classical
  rw [Convexity.StdSimplex.weights_subBarycenter, Finsupp.coe_finsetSum, Finset.sum_apply,
    Finset.sum_eq_single v]
  · simp
  · intro w hw hwv
    simp [hwv]
  · exact fun h => (h hv).elim

/-- A positive last coefficient gives exactly the final face as affine support.
No positivity of the other coefficients or nondegeneracy premise is needed. -/
theorem chainPoint_support_eq_last {n : ℕ} (σ : (faceNerve P) _⦋n⦌)
    (q : Convexity.StdSimplex ℝ (Fin (n + 1))) (hq : 0 < q.weights (Fin.last n)) :
    (chainPoint σ q).weights.support = (σ.obj (Fin.last n)).val := by
  classical
  apply Finset.Subset.antisymm (chainPoint_support_subset σ q)
  intro v hv
  rw [Finsupp.mem_support_iff]
  have hterm : 0 < q.weights (Fin.last n) *
      (Convexity.StdSimplex.subBarycenter (K := ℝ) (σ.obj (Fin.last n)).val
        (P.isRelLowerSet_faces (σ.obj (Fin.last n)).property).1).weights v := by
    rw [subBarycenter_weight_of_mem _ _ hv]
    exact mul_pos hq (inv_pos.mpr (Nat.cast_pos.mpr
      (Finset.card_pos.mpr (P.isRelLowerSet_faces (σ.obj (Fin.last n)).property).1)))
  have hle : q.weights (Fin.last n) *
      (Convexity.StdSimplex.subBarycenter (K := ℝ) (σ.obj (Fin.last n)).val
        (P.isRelLowerSet_faces (σ.obj (Fin.last n)).property).1).weights v ≤
      (chainPoint σ q).weights v := by
    rw [chainPoint, Convexity.StdSimplex.weights_iConvexComb_apply]
    exact Finset.single_le_sum (fun j _ => mul_nonneg (q.weights_nonneg j)
      ((Convexity.StdSimplex.subBarycenter (K := ℝ) (σ.obj j).val
        (P.isRelLowerSet_faces (σ.obj j).property).1).weights_nonneg v))
      (Finset.mem_univ (Fin.last n))
  exact ne_of_gt (hterm.trans_le hle)

/-- View an actual subface as a face on the vertices of a larger finite face. -/
def restrictFace (s t : Face P) (h : t.val ⊆ s.val) :
    Face (⊤ : PreAbstractSimplicialComplex s.val) := by
  classical
  refine ⟨t.val.subtype (fun v => v ∈ s.val), ?_⟩
  obtain ⟨v, hv⟩ := (P.isRelLowerSet_faces t.property).1
  exact ⟨⟨v, h hv⟩, Finset.mem_subtype.mpr hv⟩

/-- The restricted face includes back to the literal original finite face. -/
theorem finiteFaceOrderMap_restrictFace (s t : Face P) (h : t.val ⊆ s.val) :
    finiteFaceOrderMap P s (restrictFace s t h) = t := by
  classical
  apply Subtype.ext
  change (t.val.subtype (fun v => v ∈ s.val)).image (Subtype.val : s.val → V) = t.val
  ext v
  simp only [Finset.mem_image, Finset.mem_subtype]
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact hw
  · intro hv
    exact ⟨⟨v, h hv⟩, hv, rfl⟩

/-- A face chain whose faces lie in a finite face has a literal lift to that face poset. -/
def liftChainToFace (s : Face P) {n : ℕ} (σ : (faceNerve P) _⦋n⦌)
    (h : ∀ j, (σ.obj j).val ⊆ s.val) :
    (faceNerve (⊤ : PreAbstractSimplicialComplex s.val)) _⦋n⦌ := by
  classical
  exact (show Fin (n + 1) →o Face (⊤ : PreAbstractSimplicialComplex s.val) from
    { toFun := fun j => restrictFace s (σ.obj j) (h j)
      monotone' := fun i j hij => Finset.subtype_mono (σ.monotone hij) }).monotone.functor

/-- The finite-face lift maps back to the actual original chain, including all arrows. -/
theorem finiteFaceNerveMap_liftChain (s : Face P) {n : ℕ} (σ : (faceNerve P) _⦋n⦌)
    (h : ∀ j, (σ.obj j).val ⊆ s.val) :
    (finiteFaceNerveMap P s).app _ (liftChainToFace s σ h) = σ := by
  apply ComposableArrows.ext
    (h := fun j => finiteFaceOrderMap_restrictFace s (σ.obj j) (h j))
    (w := by intro j hj; subsingleton)

/-- Every realized nerve point has a finite-face presentation with that face
equal to the actual support of its affine image. -/
theorem exists_finiteFace_presentation (P : PreAbstractSimplicialComplex V)
    (a : SSet.toTop.obj (faceNerve P)) :
    ∃ (s : Face P) (z : SSet.toTop.obj (faceNerve (⊤ : PreAbstractSimplicialComplex s.val))),
      SSet.toTop.map (finiteFaceNerveMap P s) z = a ∧
        (affineToTop P a).point.weights.support = s.val := by
  obtain ⟨n, σ, _, q, hq, ha⟩ := SSet.exists_nonDegenerate_interior_presentation (faceNerve P) a
  let s := σ.obj (Fin.last n)
  let h (j : Fin (n + 1)) : (σ.obj j).val ⊆ s.val := σ.monotone (Fin.le_last j)
  let z := SSet.toTop.map (SSet.yonedaEquiv.symm (liftChainToFace s σ h))
    ((SimplexCategory.toTopHomeo.{u} ⦋n⦌).symm q)
  refine ⟨s, z, ?_, ?_⟩
  · change SSet.toTop.map (finiteFaceNerveMap P s)
      (SSet.toTop.map (SSet.yonedaEquiv.symm (liftChainToFace s σ h))
        ((SimplexCategory.toTopHomeo.{u} ⦋n⦌).symm q)) = a
    rw [realizedCell_naturality, finiteFaceNerveMap_liftChain]
    exact ha
  · rw [← ha, affineToTop_cell]
    exact chainPoint_support_eq_last σ q (hq (Fin.last n))

/-- Every weak barycentric point is attained by the actual face-nerve affine map. -/
theorem affineToTop_surjective (P : PreAbstractSimplicialComplex V) :
    Function.Surjective (affineToTop P) := by
  intro x
  let s : Face P := ⟨x.point.weights.support, x.support_mem⟩
  obtain ⟨q, hq⟩ := mem_range_support_face x
  refine ⟨SSet.toTop.map (finiteFaceNerveMap P s) ((finiteFaceHomeomorph P s).symm q), ?_⟩
  rw [affineToTop_finiteFaceMap, Homeomorph.apply_symm_apply]
  exact hq

/-- Finite affine chart uniqueness proves injectivity of the actual global map. -/
theorem affineToTop_injective (P : PreAbstractSimplicialComplex V) :
    Function.Injective (affineToTop P) := by
  intro a b hab
  obtain ⟨s, z, hz, hs⟩ := exists_finiteFace_presentation P a
  obtain ⟨t, w, hw, ht⟩ := exists_finiteFace_presentation P b
  have hst : s = t := Subtype.ext (hs.symm.trans
    ((congrArg (fun x : Realization P => x.point.weights.support) hab).trans ht))
  subst t
  have hc : faceMap P s (finiteFaceHomeomorph P s z) =
      faceMap P s (finiteFaceHomeomorph P s w) := by
    rw [← affineToTop_finiteFaceMap, ← affineToTop_finiteFaceMap, hz, hw]
    exact hab
  have hzw := (finiteFaceHomeomorph P s).injective
    ((isClosedEmbedding_faceMap P s).injective hc)
  exact hz.symm.trans ((congrArg (SSet.toTop.map (finiteFaceNerveMap P s)) hzw).trans hw)

/-- The bijection between actual face-poset points and weak barycentric points. -/
def affineEquiv (P : PreAbstractSimplicialComplex V) :
    SSet.toTop.obj (faceNerve P) ≃ Realization P :=
  Equiv.ofBijective (affineToTop P) ⟨affineToTop_injective P, affineToTop_surjective P⟩

/-- The inverse is continuous because its restriction to every finite closed face
is the inverse finite affine chart followed by the actual nerve inclusion. -/
theorem continuous_affineEquiv_symm (P : PreAbstractSimplicialComplex V) :
    Continuous (affineEquiv P).symm := by
  rw [continuous_iff]
  intro s
  have heq : (affineEquiv P).symm ∘ faceMap P s =
      SSet.toTop.map (finiteFaceNerveMap P s) ∘ (finiteFaceHomeomorph P s).symm := by
    funext q
    apply (affineEquiv P).injective
    rw [Function.comp_apply, Equiv.apply_symm_apply]
    change faceMap P s q = affineToTop P
      (SSet.toTop.map (finiteFaceNerveMap P s) ((finiteFaceHomeomorph P s).symm q))
    rw [affineToTop_finiteFaceMap, Homeomorph.apply_symm_apply]
  rw [heq]
  exact (SSet.toTop.map (finiteFaceNerveMap P s)).hom.continuous.comp
    (finiteFaceHomeomorph P s).symm.continuous

/-- The actual homeomorphism from the face-poset nerve realization to the weak
finite-face barycentric realization of an arbitrary abstract complex. -/
def affineHomeomorph (P : PreAbstractSimplicialComplex V) :
    SSet.toTop.obj (faceNerve P) ≃ₜ Realization P where
  toEquiv := affineEquiv P
  continuous_toFun := (affineToTop P).hom.continuous
  continuous_invFun := continuous_affineEquiv_symm P

/-- The actual inverse on a closed face is its finite barycentric inverse chart. -/
theorem affineHomeomorph_symm_faceMap (P : PreAbstractSimplicialComplex V) (s : Face P)
    (q : Convexity.StdSimplex ℝ s.val) :
    (affineHomeomorph P).symm (faceMap P s q) =
      SSet.toTop.map (finiteFaceNerveMap P s) ((finiteFaceHomeomorph P s).symm q) := by
  apply (affineHomeomorph P).injective
  rw [Homeomorph.apply_symm_apply]
  change faceMap P s q = affineToTop P
    (SSet.toTop.map (finiteFaceNerveMap P s) ((finiteFaceHomeomorph P s).symm q))
  rw [affineToTop_finiteFaceMap, Homeomorph.apply_symm_apply]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The homeomorphism preserves the actual inclusions of abstract subcomplexes. -/
theorem affineHomeomorph_inclusion {Q : PreAbstractSimplicialComplex V} (h : P ≤ Q)
    (z : SSet.toTop.obj (faceNerve P)) :
    affineHomeomorph Q (SSet.toTop.map (faceNerveInclusion h) z) =
      inclusion h (affineHomeomorph P z) := by
  obtain ⟨n, σ, _, q, _, rfl⟩ := SSet.exists_nonDegenerate_interior_presentation (faceNerve P) z
  change affineToTop Q (SSet.toTop.map (faceNerveInclusion h)
    (SSet.toTop.map (SSet.yonedaEquiv.symm σ)
      ((SimplexCategory.toTopHomeo.{u} ⦋n⦌).symm q))) =
    inclusion h (affineToTop P (SSet.toTop.map (SSet.yonedaEquiv.symm σ)
      ((SimplexCategory.toTopHomeo.{u} ⦋n⦌).symm q)))
  rw [realizedCell_naturality, affineToTop_cell, affineToTop_cell]
  rfl

/-- The literal singleton-face nerve vertex is carried to the literal barycentric vertex. -/
theorem affineHomeomorph_vertex (P : PreAbstractSimplicialComplex V) (v : V) (hv : {v} ∈ P) :
    affineHomeomorph P (SSet.realizedVertex (faceNerveVertex P v hv)) = vertex P v hv := by
  have hzero : (default : SSet.toTop.obj (Δ[0] : SSet.{u})) =
      (SimplexCategory.toTopHomeo.{u} ⦋0⦌).symm (Convexity.StdSimplex.single 0) :=
    Subsingleton.elim _ _
  change affineToTop P (SSet.realizedVertex (faceNerveVertex P v hv)) = _
  unfold SSet.realizedVertex
  rw [hzero, affineToTop_cell]
  apply Realization.ext
  simp [chainMap, chainPoint, faceNerveVertex, CategoryTheory.nerveEquiv, vertex]

/-- The actual inverse also preserves that specified point literally. -/
theorem affineHomeomorph_symm_vertex (P : PreAbstractSimplicialComplex V) (v : V) (hv : {v} ∈ P) :
    (affineHomeomorph P).symm (vertex P v hv) = SSet.realizedVertex (faceNerveVertex P v hv) := by
  rw [← affineHomeomorph_vertex P v hv, Homeomorph.symm_apply_apply]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Classical characteristic cells on the actual weak barycentric realization.
The cells and their finite frontier support are transported from the actual
face-poset nerve cells through the constructed affine homeomorphism. -/
@[instance_reducible]
def classicalCWComplex (P : PreAbstractSimplicialComplex V) :
    Topology.CWComplex (Set.univ : Set (Realization P)) where
  cell n := Topology.CWComplex.cell (Set.univ : Set (SSet.toTop.obj (faceNerve P))) n
  map n j := (Topology.CWComplex.map
    (C := (Set.univ : Set (SSet.toTop.obj (faceNerve P)))) n j).transEquiv
      (affineHomeomorph P).toEquiv
  source_eq n j := Topology.CWComplex.source_eq
    (C := (Set.univ : Set (SSet.toTop.obj (faceNerve P)))) n j
  continuousOn n j :=
    (affineHomeomorph P).continuous.comp_continuousOn (Topology.CWComplex.continuousOn
      (C := (Set.univ : Set (SSet.toTop.obj (faceNerve P)))) n j)
  continuousOn_symm n j :=
    (Topology.CWComplex.continuousOn_symm
      (C := (Set.univ : Set (SSet.toTop.obj (faceNerve P)))) n j).comp
      (affineHomeomorph P).symm.continuous.continuousOn (fun _ hx => hx)
  pairwiseDisjoint' := by
    intro a ha b hb hab
    apply Set.disjoint_left.mpr
    intro y hya hyb
    obtain ⟨x, hx, hxy⟩ := hya
    obtain ⟨z, hz, hzy⟩ := hyb
    have hold := Topology.CWComplex.pairwiseDisjoint'
      (C := (Set.univ : Set (SSet.toTop.obj (faceNerve P)))) ha hb hab
    exact Set.disjoint_left.mp hold ⟨x, hx, rfl⟩
      ⟨z, hz, (affineHomeomorph P).injective (hzy.trans hxy.symm)⟩
  mapsTo' n j := by
    obtain ⟨I, hI⟩ := Topology.CWComplex.mapsTo'
      (C := (Set.univ : Set (SSet.toTop.obj (faceNerve P)))) n j
    refine ⟨I, ?_⟩
    intro x hx
    have hmem := hI hx
    simp only [Set.mem_iUnion, Set.mem_image] at hmem ⊢
    obtain ⟨m, hm, k, hk, y, hy, hxy⟩ := hmem
    exact ⟨m, hm, k, hk, y, hy, congrArg (affineHomeomorph P) hxy⟩
  closed' A _ h := by
    let e := affineHomeomorph P
    have hpre : IsClosed (e ⁻¹' A) := Topology.CWComplex.closed'
      (C := (Set.univ : Set (SSet.toTop.obj (faceNerve P))))
      (e ⁻¹' A) (Set.subset_univ _) (by
        intro n j
        have hj := (h n j).preimage e.continuous
        change IsClosed (e ⁻¹' (A ∩
          ((e ∘ Topology.CWComplex.map n j) '' Metric.closedBall 0 1))) at hj
        have heq : e ⁻¹' (A ∩ ((e ∘ Topology.CWComplex.map n j) '' Metric.closedBall 0 1)) =
            e ⁻¹' A ∩ Topology.CWComplex.map n j '' Metric.closedBall 0 1 := by
          ext z
          simp only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_image, Function.comp_apply]
          constructor
          · rintro ⟨hz, x, hx, hxz⟩
            exact ⟨hz, x, hx, e.injective hxz⟩
          · rintro ⟨hz, x, hx, hxz⟩
            exact ⟨hz, x, hx, congrArg e hxz⟩
        rw [heq] at hj
        exact hj)
    simpa only [Set.image_preimage_eq A e.surjective] using e.isClosedMap _ hpre
  union' := by
    ext y
    constructor
    · intro _
      exact Set.mem_univ _
    · intro _
      have hy : (affineHomeomorph P).symm y ∈
          ⋃ (n : ℕ) (j : Topology.CWComplex.cell
            (Set.univ : Set (SSet.toTop.obj (faceNerve P))) n),
            Topology.CWComplex.map n j '' Metric.closedBall 0 1 := by
        rw [Topology.CWComplex.union']
        exact Set.mem_univ _
      simp only [Set.mem_iUnion, Set.mem_image] at hy ⊢
      obtain ⟨n, j, x, hx, hxy⟩ := hy
      refine ⟨n, j, x, hx, ?_⟩
      exact (congrArg (affineHomeomorph P) hxy).trans
        ((affineHomeomorph P).apply_symm_apply y)

/-- The weak polyhedron has its constructed classical CW structure. -/
instance instCWComplexRealization (P : PreAbstractSimplicialComplex V) :
    Topology.CWComplex (Set.univ : Set (Realization P)) := classicalCWComplex P

/-- The selected barycentric vertex is an actual classical zero cell in the
constructed weak realization, with equality at every zero-dimensional coordinate. -/
theorem vertex_is_classical_zeroCell (P : PreAbstractSimplicialComplex V) (v : V) (hv : {v} ∈ P) :
    ∃ j : Topology.CWComplex.cell (Set.univ : Set (Realization P)) 0,
      ∀ x : Fin 0 → ℝ, Topology.CWComplex.map 0 j x = vertex P v hv := by
  obtain ⟨j, hj⟩ := realizedFaceNerveVertex_is_classical_zeroCell P v hv
  refine ⟨j, ?_⟩
  intro x
  change affineHomeomorph P (Topology.CWComplex.map 0 j x) = vertex P v hv
  rw [hj x, affineHomeomorph_vertex]

end Realization

end PreAbstractSimplicialComplex

end
