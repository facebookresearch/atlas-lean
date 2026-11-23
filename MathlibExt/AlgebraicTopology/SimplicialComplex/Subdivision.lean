/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialComplex.Morphism
public import Mathlib.Data.Finset.Sort
public import Mathlib.Order.Preorder.Chain

/-!
# Actual barycentric subdivision of abstract simplicial complexes

The subdivision vertices are the actual nonempty faces. Its faces are finite
chains in their inclusion order. The coordinate realization of an order
complex is compared with the nerve of the original poset using the intrinsic
linear order on each finite chain, without ordering the ambient vertex type.

The original vertices persist as singleton faces. This is a map of belonging
vertices, rather than a simplicial map from the original complex to its
subdivision.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Topology Opposite
open scoped Simplicial

universe u

namespace PreAbstractSimplicialComplex

/-- The actual order complex: its faces are nonempty finite chains. -/
def orderComplex (α : Type u) [PartialOrder α] : PreAbstractSimplicialComplex α where
  faces := {s | s.Nonempty ∧ IsChain (· ≤ ·) (s : Set α)}
  isRelLowerSet_faces := by
    intro s hs
    refine ⟨hs.1, ?_⟩
    intro t hts ht
    exact ⟨ht, hs.2.mono hts⟩

@[simp]
theorem mem_orderComplex {α : Type u} [PartialOrder α] (s : Finset α) :
    s ∈ orderComplex α ↔ s.Nonempty ∧ IsChain (· ≤ ·) (s : Set α) := Iff.rfl

theorem singleton_mem_orderComplex {α : Type u} [PartialOrder α] (a : α) :
    ({a} : Finset α) ∈ orderComplex α := by
  simp only [mem_orderComplex, Finset.singleton_nonempty, true_and, Finset.coe_singleton]
  exact IsChain.singleton

namespace OrderComplex

variable {α : Type u} [PartialOrder α]

/-- Enumerate one actual chain in its intrinsic increasing order. -/
def faceEnumeration (s : Face (orderComplex α)) :
    Fin (s.val.card - 1 + 1) ≃o s.val := by
  classical
  letI : LinearOrder s.val := s.property.2.lt_of_le.linearOrder
  exact Fintype.orderIsoFinOfCardEq s.val (by
    rw [Fintype.card_coe]
    have hs := Finset.card_pos.mpr s.property.1
    omega)

/-- The nerve of one actual finite chain is the corresponding ordered simplex. -/
def finiteNerveIso (s : Face (orderComplex α)) :
    (Δ[s.val.card - 1] : SSet.{u}) ≅ CategoryTheory.nerve s.val :=
  (Functor.RepresentableBy.equivUliftYonedaIso
    (CategoryTheory.nerve s.val) ⦋s.val.card - 1⦌)
    (CategoryTheory.nerve.representableBy s.val (faceEnumeration s).symm)

/-- The actual finite-chain nerve chart on its original chain coordinates. -/
def finiteNerveHomeomorph (s : Face (orderComplex α)) :
    SSet.toTop.obj (CategoryTheory.nerve s.val) ≃ₜ Convexity.StdSimplex ℝ s.val :=
  (TopCat.homeoOfIso (SSet.toTop.mapIso (finiteNerveIso s)).symm).trans
    ((SimplexCategory.toTopHomeo.{u} ⦋s.val.card - 1⦌).trans
      (simplexRelabelHomeomorph (faceEnumeration s).toEquiv))

/-- The ordinal map of a chain simplex, retaining repeated vertices. -/
def simplexOrdinalMap (s : Face (orderComplex α)) {n : ℕ}
    (σ : (CategoryTheory.nerve s.val) _⦋n⦌) : ⦋n⦌ ⟶ ⦋s.val.card - 1⦌ :=
  SimplexCategory.Hom.mk
    { toFun := fun j => (faceEnumeration s).symm (σ.obj j)
      monotone' := (faceEnumeration s).symm.monotone.comp σ.monotone }

theorem finiteNerveIso_inv_app (s : Face (orderComplex α)) {n : ℕ}
    (σ : (CategoryTheory.nerve s.val) _⦋n⦌) :
    (finiteNerveIso s).inv.app _ σ =
      SSet.stdSimplex.objEquiv.symm (simplexOrdinalMap s σ) := by
  apply SSet.stdSimplex.objEquiv.injective
  apply SimplexCategory.Hom.ext
  rfl

/-- The finite chart adds all repeated-chain barycentric weights. -/
theorem finiteNerveHomeomorph_cell (s : Face (orderComplex α)) {n : ℕ}
    (σ : (CategoryTheory.nerve s.val) _⦋n⦌)
    (q : Convexity.StdSimplex ℝ (Fin (n + 1))) :
    finiteNerveHomeomorph s
      (SSet.toTop.map (SSet.yonedaEquiv.symm σ)
        ((SimplexCategory.toTopHomeo.{u} ⦋n⦌).symm q)) = q.map σ.obj := by
  change ((SimplexCategory.toTopHomeo.{u} ⦋s.val.card - 1⦌)
    (SSet.toTop.map (finiteNerveIso s).inv
      (SSet.toTop.map (SSet.yonedaEquiv.symm σ)
        ((SimplexCategory.toTopHomeo.{u} ⦋n⦌).symm q)))).map (faceEnumeration s) = _
  rw [Realization.realizedCell_naturality, finiteNerveIso_inv_app]
  have hmap : SSet.yonedaEquiv.symm
      (SSet.stdSimplex.objEquiv.symm (simplexOrdinalMap s σ)) =
        SSet.stdSimplex.map (simplexOrdinalMap s σ) := by
    apply SSet.yonedaEquiv.injective
    rw [Equiv.apply_symm_apply, SSet.yonedaEquiv_map]
  rw [hmap, SimplexCategory.toTopHomeo_naturality_apply, Homeomorph.apply_symm_apply,
    Convexity.StdSimplex.map_map]
  congr 1
  funext j
  exact (faceEnumeration s).apply_symm_apply (σ.obj j)

/-- The actual finite chain of vertices occurring in a nerve simplex. -/
def chainRange {n : ℕ} (σ : (CategoryTheory.nerve α) _⦋n⦌) :
    Face (orderComplex α) := by
  classical
  refine ⟨Finset.univ.image σ.obj, Finset.univ_nonempty.image _, ?_⟩
  simpa only [Finset.coe_image, Finset.coe_univ, Set.image_univ] using
    σ.monotone.isChain_range

/-- The literal inclusion of a finite chain in the original poset. -/
def faceOrderMap (s : Face (orderComplex α)) : s.val →o α where
  toFun := Subtype.val
  monotone' := fun _ _ h => h

/-- The nerve map of that literal finite-chain inclusion. -/
def faceNerveMap (s : Face (orderComplex α)) :
    CategoryTheory.nerve s.val ⟶ CategoryTheory.nerve α :=
  CategoryTheory.nerveMap (faceOrderMap s).monotone.functor

/-- A chain simplex whose vertices lie in an actual face lifts to that face. -/
def liftChain (s : Face (orderComplex α)) {n : ℕ}
    (σ : (CategoryTheory.nerve α) _⦋n⦌) (h : ∀ j, σ.obj j ∈ s.val) :
    (CategoryTheory.nerve s.val) _⦋n⦌ :=
  (show Fin (n + 1) →o s.val from
    { toFun := fun j => ⟨σ.obj j, h j⟩
      monotone' := σ.monotone }).monotone.functor

theorem faceNerveMap_liftChain (s : Face (orderComplex α)) {n : ℕ}
    (σ : (CategoryTheory.nerve α) _⦋n⦌) (h : ∀ j, σ.obj j ∈ s.val) :
    (faceNerveMap s).app _ (liftChain s σ h) = σ := by
  apply ComposableArrows.ext (h := fun _ => rfl)
    (w := by intro j hj; subsingleton)

/-- A nerve cell gives the finite barycentric distribution on its actual
chain vertices. Repetitions are summed by `StdSimplex.map`. -/
def cellCoordinates (α : Type u) [PartialOrder α] {n : ℕ}
    (σ : (CategoryTheory.nerve α) _⦋n⦌)
    (q : Convexity.StdSimplex ℝ (Fin (n + 1))) : Realization (orderComplex α) where
  point := q.map σ.obj
  support_mem := by
    classical
    apply ((orderComplex α).isRelLowerSet_faces (chainRange σ).property).2
    · exact (Finsupp.mapDomain_support (f := σ.obj) (s := q.weights)).trans
        (Finset.image_mono σ.obj (Finset.subset_univ _))
    · exact (q.map σ.obj).support_weights_nonempty

open Classical in
/-- The exact sum formula includes every occurrence of a repeated chain vertex. -/
theorem cellCoordinates_weights_apply {n : ℕ} (σ : (CategoryTheory.nerve α) _⦋n⦌)
    (q : Convexity.StdSimplex ℝ (Fin (n + 1))) (a : α) :
    (cellCoordinates α σ q).point.weights a =
      ∑ j : Fin (n + 1), if σ.obj j = a then q.weights j else 0 := by
  classical
  simp only [cellCoordinates, Convexity.StdSimplex.weights_map,
    Finsupp.mapDomain_fintype, Finsupp.coe_finsetSum, Finset.sum_apply,
    Finsupp.single_apply]

/-- Each actual chain-coordinate cell is continuous for the weak topology. -/
theorem continuous_cellCoordinates {n : ℕ} (σ : (CategoryTheory.nerve α) _⦋n⦌) :
    Continuous (cellCoordinates α σ) := by
  classical
  let s := chainRange σ
  let τ := liftChain s σ (fun j => Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩)
  have heq : cellCoordinates α σ =
      Realization.faceMap (orderComplex α) s ∘ Convexity.StdSimplex.map τ.obj := by
    funext q
    apply Realization.ext
    change q.map σ.obj = (q.map τ.obj).map (Subtype.val : s.val → α)
    rw [Convexity.StdSimplex.map_map]
    rfl
  rw [heq]
  exact (Realization.continuous_faceMap (orderComplex α) s).comp
    (Convexity.StdSimplex.continuous_map ℝ τ.obj)

/-- Face and degeneracy operators preserve the coordinate distribution. -/
theorem cellCoordinates_restrict {m n : ℕ} (f : ⦋m⦌ ⟶ ⦋n⦌)
    (σ : (CategoryTheory.nerve α) _⦋n⦌)
    (q : Convexity.StdSimplex ℝ (Fin (m + 1))) :
    cellCoordinates α ((CategoryTheory.nerve α).map f.op σ) q =
      cellCoordinates α σ (q.map f) := by
  apply Realization.ext
  change q.map _ = (q.map f).map σ.obj
  rw [Convexity.StdSimplex.map_map]
  rfl

/-- The compatible coordinate cells define a genuine map to the singular complex. -/
def singularMap (α : Type u) [PartialOrder α] :
    CategoryTheory.nerve α ⟶ TopCat.toSSet.obj (TopCat.of (Realization (orderComplex α))) where
  app d := ↾fun σ =>
    (TopCat.toSSetObjEquiv (TopCat.of (Realization (orderComplex α))) d).symm
      ⟨cellCoordinates α σ, continuous_cellCoordinates σ⟩
  naturality d e f := by
    obtain ⟨d, rfl⟩ : ∃ k, op (SimplexCategory.mk k) = d :=
      ⟨d.unop.len, congrArg op d.unop.mk_len⟩
    obtain ⟨e, rfl⟩ : ∃ k, op (SimplexCategory.mk k) = e :=
      ⟨e.unop.len, congrArg op e.unop.mk_len⟩
    ext σ
    apply (TopCat.toSSetObjEquiv (TopCat.of (Realization (orderComplex α)))
      (op (SimplexCategory.mk e))).injective
    apply ContinuousMap.ext
    intro q
    exact cellCoordinates_restrict f.unop σ q

/-- The actual map from the original poset nerve to its coordinate order complex. -/
def nerveToRealization (α : Type u) [PartialOrder α] :
    SSet.toTop.obj (CategoryTheory.nerve α) ⟶ TopCat.of (Realization (orderComplex α)) :=
  (sSetTopAdj.homEquiv _ _).symm (singularMap α)

/-- The global map has the literal coordinate formula on every nerve cell. -/
theorem nerveToRealization_cell {n : ℕ} (σ : (CategoryTheory.nerve α) _⦋n⦌)
    (q : Convexity.StdSimplex ℝ (Fin (n + 1))) :
    nerveToRealization α (SSet.toTop.map (SSet.yonedaEquiv.symm σ)
      ((SimplexCategory.toTopHomeo.{u} ⦋n⦌).symm q)) = cellCoordinates α σ q := by
  have hAdj := (sSetTopAdj.homEquiv (CategoryTheory.nerve α)
    (TopCat.of (Realization (orderComplex α)))).apply_symm_apply (singularMap α)
  rw [Adjunction.homEquiv_unit] at hAdj
  have hDown := congrArg (fun r => (r.app _ σ).down) hAdj
  change ((sSetTopAdj.unit.app (CategoryTheory.nerve α)).app _ σ).down ≫
    nerveToRealization α = ((singularMap α).app _ σ).down at hDown
  rw [sSetTopAdj_unit_app_app_down] at hDown
  exact ConcreteCategory.congr_hom hDown (ULift.up q)

/-- On each finite chain, the global map is its genuine finite simplex chart. -/
theorem nerveToRealization_faceMap (s : Face (orderComplex α))
    (z : SSet.toTop.obj (CategoryTheory.nerve s.val)) :
    nerveToRealization α (SSet.toTop.map (faceNerveMap s) z) =
      Realization.faceMap (orderComplex α) s (finiteNerveHomeomorph s z) := by
  obtain ⟨n, σ, _, q, _, rfl⟩ := SSet.exists_nonDegenerate_interior_presentation
    (CategoryTheory.nerve s.val) z
  rw [Realization.realizedCell_naturality, nerveToRealization_cell,
    finiteNerveHomeomorph_cell]
  apply Realization.ext
  change q.map ((faceNerveMap s).app _ σ).obj =
    (q.map σ.obj).map (Subtype.val : s.val → α)
  rw [Convexity.StdSimplex.map_map]
  rfl

/-- Positive cell coordinates have exactly the actual chain range as support,
even when the presenting chain repeats vertices. -/
theorem cellCoordinates_support_eq {n : ℕ} (σ : (CategoryTheory.nerve α) _⦋n⦌)
    (q : Convexity.StdSimplex ℝ (Fin (n + 1))) (hq : ∀ j, 0 < q.weights j) :
    (cellCoordinates α σ q).point.weights.support = (chainRange σ).val := by
  classical
  apply Finset.Subset.antisymm
  · exact (Finsupp.mapDomain_support (f := σ.obj) (s := q.weights)).trans
      (Finset.image_mono σ.obj (Finset.subset_univ _))
  · intro a ha
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp ha
    rw [Finsupp.mem_support_iff, cellCoordinates_weights_apply]
    apply ne_of_gt
    apply lt_of_lt_of_le (hq j)
    simpa using
      (Finset.single_le_sum (s := Finset.univ)
        (f := fun i : Fin (n + 1) => if σ.obj i = σ.obj j then q.weights i else 0)
        (fun i _ => by
          split_ifs
          · exact q.weights_nonneg i
          · exact le_rfl) (Finset.mem_univ j))

/-- Every nerve point has a finite-chain chart whose vertices are exactly its
coordinate support. -/
theorem exists_face_presentation (a : SSet.toTop.obj (CategoryTheory.nerve α)) :
    ∃ (s : Face (orderComplex α)) (z : SSet.toTop.obj (CategoryTheory.nerve s.val)),
      SSet.toTop.map (faceNerveMap s) z = a ∧
        (nerveToRealization α a).point.weights.support = s.val := by
  classical
  obtain ⟨n, σ, _, q, hq, ha⟩ :=
    SSet.exists_nonDegenerate_interior_presentation (CategoryTheory.nerve α) a
  let s := chainRange σ
  let h (j : Fin (n + 1)) : σ.obj j ∈ s.val :=
    Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
  let z := SSet.toTop.map (SSet.yonedaEquiv.symm (liftChain s σ h))
    ((SimplexCategory.toTopHomeo.{u} ⦋n⦌).symm q)
  refine ⟨s, z, ?_, ?_⟩
  · rw [Realization.realizedCell_naturality, faceNerveMap_liftChain]
    exact ha
  · rw [← ha, nerveToRealization_cell]
    exact cellCoordinates_support_eq σ q hq

/-- Every weak coordinate point is attained by the constructed nerve map. -/
theorem nerveToRealization_surjective (α : Type u) [PartialOrder α] :
    Function.Surjective (nerveToRealization α) := by
  intro x
  let s : Face (orderComplex α) := ⟨x.point.weights.support, x.support_mem⟩
  obtain ⟨q, hq⟩ := Realization.mem_range_support_face x
  refine ⟨SSet.toTop.map (faceNerveMap s) ((finiteNerveHomeomorph s).symm q), ?_⟩
  rw [nerveToRealization_faceMap, Homeomorph.apply_symm_apply]
  exact hq

/-- Exact support and the genuine finite charts prove global injectivity. -/
theorem nerveToRealization_injective (α : Type u) [PartialOrder α] :
    Function.Injective (nerveToRealization α) := by
  intro a b hab
  obtain ⟨s, z, hz, hs⟩ := exists_face_presentation a
  obtain ⟨t, w, hw, ht⟩ := exists_face_presentation b
  have hst : s = t := Subtype.ext (hs.symm.trans
    ((congrArg (fun x : Realization (orderComplex α) => x.point.weights.support) hab).trans ht))
  subst t
  have hc : Realization.faceMap (orderComplex α) s (finiteNerveHomeomorph s z) =
      Realization.faceMap (orderComplex α) s (finiteNerveHomeomorph s w) := by
    rw [← nerveToRealization_faceMap, ← nerveToRealization_faceMap, hz, hw]
    exact hab
  have hzw := (finiteNerveHomeomorph s).injective
    ((Realization.isClosedEmbedding_faceMap (orderComplex α) s).injective hc)
  exact hz.symm.trans ((congrArg (SSet.toTop.map (faceNerveMap s)) hzw).trans hw)

/-- The proved bijection between original nerve points and order-complex coordinates. -/
def realizationEquiv (α : Type u) [PartialOrder α] :
    SSet.toTop.obj (CategoryTheory.nerve α) ≃ Realization (orderComplex α) :=
  Equiv.ofBijective (nerveToRealization α)
    ⟨nerveToRealization_injective α, nerveToRealization_surjective α⟩

/-- The inverse is continuous on every actual closed finite-chain face. -/
theorem continuous_realizationEquiv_symm (α : Type u) [PartialOrder α] :
    Continuous (realizationEquiv α).symm := by
  rw [Realization.continuous_iff]
  intro s
  have heq : (realizationEquiv α).symm ∘ Realization.faceMap (orderComplex α) s =
      SSet.toTop.map (faceNerveMap s) ∘ (finiteNerveHomeomorph s).symm := by
    funext q
    apply (realizationEquiv α).injective
    rw [Function.comp_apply, Equiv.apply_symm_apply]
    change Realization.faceMap (orderComplex α) s q = nerveToRealization α
      (SSet.toTop.map (faceNerveMap s) ((finiteNerveHomeomorph s).symm q))
    rw [nerveToRealization_faceMap, Homeomorph.apply_symm_apply]
  rw [heq]
  exact (SSet.toTop.map (faceNerveMap s)).hom.continuous.comp
    (finiteNerveHomeomorph s).symm.continuous

end OrderComplex

/-- The coordinate order complex is homeomorphic to the nerve of the original
poset, with both maps constructed from actual finite-chain charts. -/
def orderComplexHomeomorph (α : Type u) [PartialOrder α] :
    Realization (orderComplex α) ≃ₜ SSet.toTop.obj (CategoryTheory.nerve α) where
  toEquiv := (OrderComplex.realizationEquiv α).symm
  continuous_toFun := OrderComplex.continuous_realizationEquiv_symm α
  continuous_invFun := (OrderComplex.nerveToRealization α).hom.continuous

/-- The inverse has the literal sum-of-chain-weights formula on every cell. -/
theorem orderComplexHomeomorph_symm_cell {α : Type u} [PartialOrder α] {n : ℕ}
    (σ : (CategoryTheory.nerve α) _⦋n⦌)
    (q : Convexity.StdSimplex ℝ (Fin (n + 1))) :
    (orderComplexHomeomorph α).symm
      (SSet.toTop.map (SSet.yonedaEquiv.symm σ)
        ((SimplexCategory.toTopHomeo.{u} ⦋n⦌).symm q)) =
      OrderComplex.cellCoordinates α σ q :=
  OrderComplex.nerveToRealization_cell σ q

/-- The forward map on a closed chain face is the actual inverse ordinal chart. -/
theorem orderComplexHomeomorph_faceMap {α : Type u} [PartialOrder α]
    (s : Face (orderComplex α)) (q : Convexity.StdSimplex ℝ s.val) :
    orderComplexHomeomorph α (Realization.faceMap (orderComplex α) s q) =
      SSet.toTop.map (OrderComplex.faceNerveMap s)
        ((OrderComplex.finiteNerveHomeomorph s).symm q) := by
  apply (orderComplexHomeomorph α).symm.injective
  rw [Homeomorph.symm_apply_apply]
  change Realization.faceMap (orderComplex α) s q =
    OrderComplex.nerveToRealization α (SSet.toTop.map (OrderComplex.faceNerveMap s)
      ((OrderComplex.finiteNerveHomeomorph s).symm q))
  rw [OrderComplex.nerveToRealization_faceMap, Homeomorph.apply_symm_apply]

set_option backward.isDefEq.respectTransparency false in
/-- Every poset element remains its literal nerve vertex. -/
theorem orderComplexHomeomorph_vertex {α : Type u} [PartialOrder α] (a : α) :
    orderComplexHomeomorph α
      (Realization.vertex (orderComplex α) a (singleton_mem_orderComplex a)) =
      SSet.realizedVertex (CategoryTheory.nerveEquiv.symm a) := by
  apply (orderComplexHomeomorph α).symm.injective
  rw [Homeomorph.symm_apply_apply]
  have hzero : (default : SSet.toTop.obj (Δ[0] : SSet.{u})) =
      (SimplexCategory.toTopHomeo.{u} ⦋0⦌).symm (Convexity.StdSimplex.single 0) :=
    Subsingleton.elim _ _
  unfold SSet.realizedVertex
  rw [hzero, orderComplexHomeomorph_symm_cell]
  apply Realization.ext
  simp [OrderComplex.cellCoordinates, CategoryTheory.nerveEquiv, Realization.vertex]

variable {V : Type u}

/-- The actual barycentric subdivision on the original nonempty face type. -/
def barycentricSubdivision (P : PreAbstractSimplicialComplex V) :
    PreAbstractSimplicialComplex (Face P) := orderComplex (Face P)

@[simp]
theorem mem_barycentricSubdivision (P : PreAbstractSimplicialComplex V)
    (s : Finset (Face P)) :
    s ∈ barycentricSubdivision P ↔ s.Nonempty ∧ IsChain (· ≤ ·) (s : Set (Face P)) :=
  Iff.rfl

/-- The actual subdivision homeomorphism uses the original face-poset nerve. -/
def barycentricHomeomorph (P : PreAbstractSimplicialComplex V) :
    Realization (barycentricSubdivision P) ≃ₜ Realization P :=
  (orderComplexHomeomorph (Face P)).trans (Realization.affineHomeomorph P)

set_option backward.isDefEq.respectTransparency false in
/-- The exact affine formula uses the original finite-face barycenters. -/
theorem barycentricHomeomorph_point (P : PreAbstractSimplicialComplex V)
    (x : Realization (barycentricSubdivision P)) :
    (barycentricHomeomorph P x).point =
      x.point.iConvexComb (fun s : Face P => Convexity.StdSimplex.subBarycenter
        s.val (P.isRelLowerSet_faces s.property).1) := by
  obtain ⟨z, rfl⟩ := (orderComplexHomeomorph (Face P)).symm.surjective x
  have hz : (barycentricHomeomorph P ((orderComplexHomeomorph (Face P)).symm z)).point =
      (Realization.affineHomeomorph P z).point :=
    congrArg (fun y => (Realization.affineHomeomorph P y).point)
      ((orderComplexHomeomorph (Face P)).apply_symm_apply z)
  rw [hz]
  obtain ⟨n, σ, _, q, _, rfl⟩ :=
    SSet.exists_nonDegenerate_interior_presentation (CategoryTheory.nerve (Face P)) z
  change (Realization.affineToTop P
    (SSet.toTop.map (SSet.yonedaEquiv.symm σ)
      ((SimplexCategory.toTopHomeo.{u} ⦋n⦌).symm q))).point =
    (OrderComplex.nerveToRealization (Face P)
      (SSet.toTop.map (SSet.yonedaEquiv.symm σ)
        ((SimplexCategory.toTopHomeo.{u} ⦋n⦌).symm q))).point.iConvexComb _
  erw [Realization.affineToTop_cell, OrderComplex.nerveToRealization_cell]
  change Realization.chainPoint σ q = (q.map σ.obj).iConvexComb _
  rw [Convexity.iConvexComb_map]
  rfl

/-- On each actual subdivision face the barycentric weights are its vertex
weights applied to the centroids of the corresponding original faces. -/
theorem barycentricHomeomorph_faceMap_point (P : PreAbstractSimplicialComplex V)
    (s : Face (barycentricSubdivision P)) (q : Convexity.StdSimplex ℝ s.val) :
    (barycentricHomeomorph P (Realization.faceMap (barycentricSubdivision P) s q)).point =
      q.iConvexComb (fun a : s.val => Convexity.StdSimplex.subBarycenter
        a.val.val (P.isRelLowerSet_faces a.val.property).1) := by
  rw [barycentricHomeomorph_point]
  exact Convexity.iConvexComb_map q (Subtype.val : s.val → Face P) _

/-- An original belonging vertex persists as its actual singleton face. -/
def singletonSubdivisionVertex (P : PreAbstractSimplicialComplex V) (v : Vertex P) :
    Vertex (barycentricSubdivision P) :=
  ⟨⟨{v.val}, v.property⟩, singleton_mem_orderComplex _⟩

/-- The subdivision homeomorphism fixes each persistent original vertex literally. -/
theorem barycentricHomeomorph_singletonVertex (P : PreAbstractSimplicialComplex V)
    (v : Vertex P) :
    barycentricHomeomorph P
      (Realization.vertex (barycentricSubdivision P)
        (singletonSubdivisionVertex P v).val (singletonSubdivisionVertex P v).property) =
      Realization.vertex P v.val v.property := by
  change Realization.affineHomeomorph P
    (orderComplexHomeomorph (Face P)
      (Realization.vertex (orderComplex (Face P)) ⟨{v.val}, v.property⟩ _)) = _
  rw [orderComplexHomeomorph_vertex]
  exact Realization.affineHomeomorph_vertex P v.val v.property

/-- The inverse has the same literal persistent original point. -/
theorem barycentricHomeomorph_symm_vertex (P : PreAbstractSimplicialComplex V)
    (v : Vertex P) :
    (barycentricHomeomorph P).symm (Realization.vertex P v.val v.property) =
      Realization.vertex (barycentricSubdivision P)
        (singletonSubdivisionVertex P v).val (singletonSubdivisionVertex P v).property := by
  rw [← barycentricHomeomorph_singletonVertex P v, Homeomorph.symm_apply_apply]

/-- The successive actual vertex types and complexes, with no ambient labels added. -/
def barycentricIteration (P : PreAbstractSimplicialComplex V) (n : ℕ) :
    Σ W : Type u, PreAbstractSimplicialComplex W :=
  match n with
  | 0 => ⟨V, P⟩
  | n + 1 =>
      let Q := barycentricIteration P n
      ⟨Face Q.2, barycentricSubdivision Q.2⟩

/-- The actual ambient vertex type of the finite iterate. -/
abbrev subdivisionVertexType (P : PreAbstractSimplicialComplex V) (n : ℕ) : Type u :=
  (barycentricIteration P n).1

/-- The actual complex after the specified finite number of subdivisions. -/
abbrev subdivisionIter (P : PreAbstractSimplicialComplex V) (n : ℕ) :
    PreAbstractSimplicialComplex (subdivisionVertexType P n) := (barycentricIteration P n).2

@[simp]
theorem subdivisionIter_zero (P : PreAbstractSimplicialComplex V) : subdivisionIter P 0 = P := rfl

@[simp]
theorem subdivisionIter_succ (P : PreAbstractSimplicialComplex V) (n : ℕ) :
    subdivisionIter P (n + 1) = barycentricSubdivision (subdivisionIter P n) := rfl

/-- The finite-iterate homeomorphism is the composition of the constructed maps. -/
def iteratedHomeomorph (P : PreAbstractSimplicialComplex V) (n : ℕ) :
    Realization (subdivisionIter P n) ≃ₜ Realization P :=
  match n with
  | 0 => Homeomorph.refl _
  | n + 1 => (barycentricHomeomorph (subdivisionIter P n)).trans (iteratedHomeomorph P n)

/-- Original belonging vertices persist as successive literal singleton faces. -/
def persistentVertex (P : PreAbstractSimplicialComplex V) (n : ℕ) (v : Vertex P) :
    Vertex (subdivisionIter P n) :=
  match n with
  | 0 => v
  | n + 1 => singletonSubdivisionVertex (subdivisionIter P n) (persistentVertex P n v)

/-- Every finite iterate sends its persistent original vertex to that exact point. -/
theorem iteratedHomeomorph_persistentVertex (P : PreAbstractSimplicialComplex V)
    (n : ℕ) (v : Vertex P) :
    iteratedHomeomorph P n
      (Realization.vertex (subdivisionIter P n)
        (persistentVertex P n v).val (persistentVertex P n v).property) =
      Realization.vertex P v.val v.property := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change iteratedHomeomorph P n
        (barycentricHomeomorph (subdivisionIter P n)
          (Realization.vertex (barycentricSubdivision (subdivisionIter P n))
            (singletonSubdivisionVertex (subdivisionIter P n) (persistentVertex P n v)).val
            (singletonSubdivisionVertex (subdivisionIter P n)
                (persistentVertex P n v)).property)) = _
      rw [barycentricHomeomorph_singletonVertex]
      exact ih

/-- The inverse finite-iterate map also preserves the exact persistent point. -/
theorem iteratedHomeomorph_symm_vertex (P : PreAbstractSimplicialComplex V)
    (n : ℕ) (v : Vertex P) :
    (iteratedHomeomorph P n).symm (Realization.vertex P v.val v.property) =
      Realization.vertex (subdivisionIter P n)
        (persistentVertex P n v).val (persistentVertex P n v).property := by
  rw [← iteratedHomeomorph_persistentVertex P n v, Homeomorph.symm_apply_apply]

/-- A finite actual face set has a finite subdivision face set, even when the
original ambient vertex type has infinitely many ghost labels. -/
theorem finiteFaces_barycentricSubdivision (P : PreAbstractSimplicialComplex V)
    [Finite (Face P)] : Finite (Face (barycentricSubdivision P)) := by
  let := Fintype.ofFinite (Face P)
  exact Finite.of_injective Subtype.val Subtype.val_injective

/-- All actual finite iterates retain finiteness of the original face set. -/
theorem finiteFaces_subdivisionIter (P : PreAbstractSimplicialComplex V)
    [Finite (Face P)] (n : ℕ) : Finite (Face (subdivisionIter P n)) := by
  induction n with
  | zero =>
      change Finite (Face P)
      exact inferInstance
  | succ n ih =>
      have := ih
      exact finiteFaces_barycentricSubdivision (subdivisionIter P n)

/-- The largest original face of an actual subdivision face. -/
def subdivisionLastFace (P : PreAbstractSimplicialComplex V)
    (s : Face (barycentricSubdivision P)) : Face P :=
  (OrderComplex.faceEnumeration s (Fin.last (s.val.card - 1))).val

/-- Every vertex face in a subdivision face is contained in its actual last face. -/
theorem le_subdivisionLastFace (P : PreAbstractSimplicialComplex V)
    (s : Face (barycentricSubdivision P)) (a : s.val) : a.val ≤ subdivisionLastFace P s := by
  change a ≤ OrderComplex.faceEnumeration s (Fin.last (s.val.card - 1))
  simpa only [OrderIso.apply_symm_apply] using
    (OrderComplex.faceEnumeration s).monotone
      (Fin.le_last ((OrderComplex.faceEnumeration s).symm a))

/-- Each vertex centroid is expressed on the actual vertices of the largest face. -/
def subdivisionFaceVertexCoordinates (P : PreAbstractSimplicialComplex V)
    (s : Face (barycentricSubdivision P)) (a : s.val) :
    Convexity.StdSimplex ℝ (subdivisionLastFace P s).val :=
  let t := Realization.restrictFace (subdivisionLastFace P s) a.val
    (le_subdivisionLastFace P s a)
  Convexity.StdSimplex.subBarycenter t.val t.property

/-- Forgetting the largest-face subtype gives the exact original-face centroid. -/
theorem map_subdivisionFaceVertexCoordinates (P : PreAbstractSimplicialComplex V)
    (s : Face (barycentricSubdivision P)) (a : s.val) :
    (subdivisionFaceVertexCoordinates P s a).map
        (Subtype.val : (subdivisionLastFace P s).val → V) =
      Convexity.StdSimplex.subBarycenter a.val.val
        (P.isRelLowerSet_faces a.val.property).1 := by
  classical
  unfold subdivisionFaceVertexCoordinates
  rw [Realization.map_subBarycenter_injective
    (Subtype.val : (subdivisionLastFace P s).val → V) Subtype.val_injective]
  congr 1
  exact congrArg Subtype.val
    (Realization.finiteFaceOrderMap_restrictFace (subdivisionLastFace P s) a.val
      (le_subdivisionLastFace P s a))

/-- The actual affine chart from a subdivision face into its largest original face. -/
def barycentricFaceCoordinates (P : PreAbstractSimplicialComplex V)
    (s : Face (barycentricSubdivision P)) :
    Convexity.ConvexSpace.AffineMap ℝ (Convexity.StdSimplex ℝ s.val)
      (Convexity.StdSimplex ℝ (subdivisionLastFace P s).val) :=
  Convexity.StdSimplex.affineMapMk (subdivisionFaceVertexCoordinates P s)

/-- The subdivision homeomorphism has its actual finite affine chart on every face. -/
theorem barycentricHomeomorph_faceMap (P : PreAbstractSimplicialComplex V)
    (s : Face (barycentricSubdivision P)) (q : Convexity.StdSimplex ℝ s.val) :
    barycentricHomeomorph P (Realization.faceMap (barycentricSubdivision P) s q) =
      Realization.faceMap P (subdivisionLastFace P s) (barycentricFaceCoordinates P s q) := by
  apply Realization.ext
  rw [barycentricHomeomorph_faceMap_point]
  change q.iConvexComb _ =
    (q.iConvexComb (subdivisionFaceVertexCoordinates P s)).map
      (Subtype.val : (subdivisionLastFace P s).val → V)
  rw [Convexity.map_iConvexComb]
  apply Convexity.iConvexComb_congr
  intro a _
  exact (map_subdivisionFaceVertexCoordinates P s a).symm

/-- Every actual iterated face is affine in the original barycentric coordinates.
This property is derived from the finite charts at each step. -/
theorem isAffineMap_iteratedHomeomorph_faceMap (P : PreAbstractSimplicialComplex V)
    (n : ℕ) (s : Face (subdivisionIter P n)) :
    Convexity.IsAffineMap ℝ (fun q : Convexity.StdSimplex ℝ s.val =>
      (iteratedHomeomorph P n (Realization.faceMap (subdivisionIter P n) s q)).point) := by
  induction n with
  | zero =>
      change Convexity.IsAffineMap ℝ (Convexity.StdSimplex.map (Subtype.val : s.val → V))
      exact Convexity.StdSimplex.isAffineMap_map ℝ _
  | succ n ih =>
      let t := subdivisionLastFace (subdivisionIter P n) s
      have heq : (fun q : Convexity.StdSimplex ℝ s.val =>
          (iteratedHomeomorph P (n + 1)
            (Realization.faceMap (subdivisionIter P (n + 1)) s q)).point) =
          (fun q : Convexity.StdSimplex ℝ t.val =>
            (iteratedHomeomorph P n (Realization.faceMap (subdivisionIter P n) t q)).point) ∘
          barycentricFaceCoordinates (subdivisionIter P n) s := by
        funext q
        change (iteratedHomeomorph P n
          (barycentricHomeomorph (subdivisionIter P n)
            (Realization.faceMap (barycentricSubdivision (subdivisionIter P n)) s q))).point = _
        erw [barycentricHomeomorph_faceMap]
        rfl
      rw [heq]
      exact (ih t).comp (barycentricFaceCoordinates (subdivisionIter P n) s).isAffineMap

/-- The complete iterate face formula uses the exact images of its finite face vertices. -/
theorem iteratedHomeomorph_faceMap_point (P : PreAbstractSimplicialComplex V)
    (n : ℕ) (s : Face (subdivisionIter P n)) (q : Convexity.StdSimplex ℝ s.val) :
    (iteratedHomeomorph P n (Realization.faceMap (subdivisionIter P n) s q)).point =
      q.iConvexComb (fun a : s.val =>
        (iteratedHomeomorph P n
          (Realization.faceMap (subdivisionIter P n) s
              (Convexity.StdSimplex.single a))).point) := by
  have h := (isAffineMap_iteratedHomeomorph_faceMap P n s).map_iConvexComb q
    (Convexity.StdSimplex.single : s.val → Convexity.StdSimplex ℝ s.val)
  simpa only [Convexity.StdSimplex.iConvexComb_single, Function.comp_def] using h

/-- A chain of distinct nonempty subfaces has at most as many members as its last face. -/
theorem card_subdivisionFace_le_lastFace (P : PreAbstractSimplicialComplex V)
    (s : Face (barycentricSubdivision P)) : s.val.card ≤ (subdivisionLastFace P s).val.card := by
  classical
  let e := OrderComplex.faceEnumeration s
  let f (j : Fin (s.val.card - 1 + 1)) : ℕ := (e j).val.val.card
  have hf : StrictMono f := by
    intro i j hij
    exact Finset.card_lt_card (e.strictMono hij)
  have hbound (j : Fin (s.val.card - 1 + 1)) : j.val + 1 ≤ f j := by
    refine Fin.induction ?_ ?_ j
    · have h0 : 0 < f 0 :=
        Finset.card_pos.mpr (P.isRelLowerSet_faces (e 0).val.property).1
      simpa only [Fin.val_zero] using Nat.succ_le_of_lt h0
    · intro i hi
      have hstep := hf (Fin.castSucc_lt_succ (i := i))
      change i.val + 1 ≤ f i.castSucc at hi
      change i.val + 2 ≤ f i.succ
      omega
  have hs : s.val.card - 1 + 1 = s.val.card := by
    have hpos := Finset.card_pos.mpr s.property.1
    omega
  change s.val.card ≤ f (Fin.last (s.val.card - 1))
  simpa only [Fin.val_last, hs] using hbound (Fin.last (s.val.card - 1))

/-- An actual uniform original face-cardinality bound is retained by every finite iterate. -/
theorem card_subdivisionIter_face_le (P : PreAbstractSimplicialComplex V) (M : ℕ)
    (hP : ∀ s : Face P, s.val.card ≤ M) (n : ℕ) (s : Face (subdivisionIter P n)) :
    s.val.card ≤ M := by
  induction n with
  | zero => exact hP s
  | succ n ih =>
      exact (card_subdivisionFace_le_lastFace (subdivisionIter P n) s).trans
        (ih (subdivisionLastFace (subdivisionIter P n) s))

/-- Finitely many actual original faces give one cardinality bound for all iterates,
including geometrically empty complexes with arbitrary ambient ghost labels. -/
theorem exists_uniform_subdivisionIter_card_bound (P : PreAbstractSimplicialComplex V)
    [Finite (Face P)] :
    ∃ N : ℕ, ∀ (n : ℕ) (s : Face (subdivisionIter P n)), s.val.card ≤ N + 1 := by
  classical
  let := Fintype.ofFinite (Face P)
  let N := ∑ s : Face P, s.val.card
  refine ⟨N, fun n s => card_subdivisionIter_face_le P (N + 1) ?_ n s⟩
  intro a
  have h := Finset.single_le_sum (s := Finset.univ) (f := fun s : Face P => s.val.card)
    (fun s _ => Nat.zero_le _) (Finset.mem_univ a)
  exact h.trans (Nat.le_succ N)

end PreAbstractSimplicialComplex

end
