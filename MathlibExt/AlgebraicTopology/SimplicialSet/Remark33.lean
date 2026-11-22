/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.HornDescent
public import MathlibExt.AlgebraicTopology.Quasicategory.CoreKan
public import MathlibExt.AlgebraicTopology.Quasicategory.SpecialOuterHornGeneral
public import MathlibExt.AlgebraicTopology.SimplicialSet.JoinNaturality

/-!
# Remark 3.3: left mapping spaces are Kan complexes

Now let `Λ[m, i] ⟶ H` be a horn, `m ≥ 2`, given as a compatible
family of `(m - 1)`-simplices `f_j` of `H` for `j ≠ i`.
Transporting, we get `m`-simplices `s_j` of `X`, each with
`0`-th vertex `x` and `δ₀s_j` constant at `y`, pairwise
compatible. Adjoin one more face: the constant `m`-simplex at
`y` as face `0`. It is compatible with every `s_j`: one side of
the compatibility is a face of a constant simplex, the other is
`δ₀s_j`, constant at `y` by the mapping-space condition. We
have built a horn `Λ[m + 1, i + 1] ⟶ X` (indices shifted by
one: `s_j` is face `j + 1`) whose `0`-th face is constant.

The second bullet is *not* a consequence of Definition 3.1 by
any argument in this file: Stevenson asserts
Remark 3.3 for pre-fibrant `S` without proof (see the header of
`HornDescent.lean`), and Joyal's special
outer horn filling is landed only for quasicategories
(`SSet.hasSpecialOuterHornFilling_of_quasicategory`). We
therefore name the input explicitly, as the predicate
`SSet.HasSpecialRightHornFillingWithConstantZeroFace`:
right outer horns with constant `0`-th face fill — proved for
all pre-fibrant `S` in the sibling module
`PreFibrantSpecialHorn.lean`
(`SSet.hasSpecialRightHornFillingWithConstantZeroFace_of_isPreFibrant`,
discharging the additional comparison obligation). With it, the
horn transport above is complete:
-/

@[expose] public section

noncomputable section

open CategoryTheory MonoidalCategory Limits Opposite
open scoped Simplicial
open scoped CategoryTheory.MonoidalCategory.DayFunctor

universe u

namespace SSet

/-! ## §1. The transported back face is `δ₀`

Mirror of the Yoneda-element chase for `joinInl`
(`SSet.Join.joinInlDay_eq`,
`SSet.joinInl_comp_joinStdSimplexIso_hom`,
`SSet.frontInclusion_eq`): `joinInr` expands through the *left*
Day unitor and whiskering on the right; the element-level
inputs are `SSet.Join.leftUnitor_inv_app_of` and
`SSet.Join.inr_of_eq`, together with the component lemmas
(`SSet.Join.augDayStdSimplexIso_hom_app_of`,
`..._app_star`, `..._inv_app_of`,
`SSet.Join.augDayBotIso_inv_app_star`,
`SSet.Join.augDay_map_initial_to_app_star`). -/

/-- The transported back face is `inr'`: this is
`SSet.joinInr_comp_joinStdSimplexIso_hom` at `m = 0`. Mirror of
`SSet.leftVertex_eq`. -/
theorem backInclusion_eq (n : ℕ) :
    backInclusion.{u} n =
      SSet.stdSimplex.map (AugmentedSimplexCategory.inr' ⦋0⦌ ⦋n⦌) :=
  joinInr_comp_joinStdSimplexIso_hom 0 n

/-- **`backInclusionSucc` is `δ₀`**: the transported back face,
read in `Δ[n + 1]` through `SSet.zeroAddSuccIso`, is the
standard `0`-th face map. This closes the additional comparison obligation
of `HornDescent.lean`; mirror of the supporting results
`SSet.frontInclusion_eq` and companion to the supporting result
`SSet.leftVertexSucc_eq`. -/
theorem backInclusionSucc_eq (n : ℕ) :
    backInclusionSucc.{u} n = stdSimplex.δ (0 : Fin (n + 2)) := by
  rw [backInclusionSucc, backInclusion_eq, ← Functor.map_comp,
    inr'_zero_comp_zeroAddSuccIso_hom]
  exact (stdSimplex_δ_eq_map _).symm

/-! ## §2. Simplices of the left mapping space in standard form

Composing the landed transport
`SSet.mappingSpaceLeft.simplexEquivSucc` (along
`SSet.joinStdSimplexIso 0 n`, landing in `Δ[0 + n + 1]`) with
precomposition by `SSet.zeroAddSuccIso` and using the supporting result
`SSet.leftVertexSucc_eq` and §1's `SSet.backInclusionSucc_eq`,
the `n`-simplices of `SSet.mappingSpaceLeft X x y` are the
`(n + 1)`-simplices of `X` with `0`-th vertex `x` and `0`-th
(back) face the constant simplex at `y` — Stevenson's §2.4
description of `Homᴸ`. Face maps correspond to the shifted
face maps `δ (succ a)`. -/

/-- The `0`-th vertex inclusion followed by a face map that
does not omit vertex `0` is the `0`-th vertex inclusion one
dimension up. The left analogue of the relation
`SSet.rightVertex_comp_δ_castSucc` of the supporting results; here the
vertex is already identified (`SSet.leftVertexSucc_eq`), so
this is the simplex-category computation
`const 0 ≫ δ (succ j) = const 0`. -/
lemma vertexZero_comp_δ_succ {n : ℕ} (j : Fin (n + 2)) :
    SSet.stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋n + 1⦌ 0) ≫
        stdSimplex.δ j.succ =
      SSet.stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋n + 2⦌ 0) := by
  rw [stdSimplex_δ_eq_map, ← Functor.map_comp]
  congr 1

namespace mappingSpaceLeft

variable (X : SSet.{u}) (x y : (Δ[0] : SSet.{u}) ⟶ X)

/-- The `n`-simplices of `mappingSpaceLeft X x y`, read in
`Δ[n + 1]` through `SSet.zeroAddSuccIso n`: the `(n + 1)`-simplices
`σ` of `X` whose `0`-th vertex is `x` and whose `0`-th (back)
face `stdSimplex.δ 0 ≫ σ` is the constant `n`-simplex at `y`.
This is Stevenson's §2.4 description of `Homᴸ_X(x, y)`,
obtained from the landed `SSet.mappingSpaceLeft.simplexEquivSucc`
by the endpoint identifications `SSet.leftVertexSucc_eq`
(the supporting results) and `SSet.backInclusionSucc_eq` (§1). -/
def simplexEquivSuccStd (n : ℕ) :
    (mappingSpaceLeft X x y).obj (op ⦋n⦌) ≃
      { σ : (Δ[n + 1] : SSet.{u}) ⟶ X //
        SSet.stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋n + 1⦌ 0) ≫ σ = x ∧
          stdSimplex.δ (0 : Fin (n + 2)) ≫ σ =
            toDeltaZero Δ[n] ≫ y } where
  toFun f :=
    ⟨SSet.stdSimplex.map (zeroAddSuccIso n).inv ≫
      ((simplexEquivSucc X x y n) f).1, by
      have e1 : SSet.stdSimplex.map
              (SimplexCategory.const ⦋0⦌ ⦋n + 1⦌ 0) ≫
            SSet.stdSimplex.map (zeroAddSuccIso n).inv =
          leftVertex n := by
        have h : leftVertex n ≫
              SSet.stdSimplex.map (zeroAddSuccIso n).hom =
            SSet.stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋n + 1⦌ 0) :=
          leftVertexSucc_eq n
        rw [← h, Category.assoc, ← Functor.map_comp, Iso.hom_inv_id,
          CategoryTheory.Functor.map_id, Category.comp_id]
      have e2 : stdSimplex.δ (0 : Fin (n + 2)) ≫
            SSet.stdSimplex.map (zeroAddSuccIso n).inv =
          backInclusion n := by
        have h : backInclusion n ≫
              SSet.stdSimplex.map (zeroAddSuccIso n).hom =
            stdSimplex.δ (0 : Fin (n + 2)) :=
          backInclusionSucc_eq n
        rw [← h, Category.assoc, ← Functor.map_comp, Iso.hom_inv_id,
          CategoryTheory.Functor.map_id, Category.comp_id]
      constructor
      · rw [← Category.assoc, e1]
        exact ((simplexEquivSucc X x y n) f).2.1
      · rw [← Category.assoc, e2]
        exact ((simplexEquivSucc X x y n) f).2.2⟩
  invFun σ :=
    (simplexEquivSucc X x y n).symm
      ⟨SSet.stdSimplex.map (zeroAddSuccIso n).hom ≫ σ.1, by
        have e1 : leftVertex n ≫
              SSet.stdSimplex.map (zeroAddSuccIso n).hom =
            SSet.stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋n + 1⦌ 0) :=
          leftVertexSucc_eq n
        have e2 : backInclusion n ≫
              SSet.stdSimplex.map (zeroAddSuccIso n).hom =
            stdSimplex.δ (0 : Fin (n + 2)) :=
          backInclusionSucc_eq n
        constructor
        · rw [← Category.assoc, e1]
          exact σ.2.1
        · rw [← Category.assoc, e2]
          exact σ.2.2⟩
  left_inv f := by
    apply (simplexEquivSucc X x y n).injective
    rw [Equiv.apply_symm_apply]
    apply Subtype.ext
    change SSet.stdSimplex.map (zeroAddSuccIso n).hom ≫
        (SSet.stdSimplex.map (zeroAddSuccIso n).inv ≫
          ((simplexEquivSucc X x y n) f).1) =
      ((simplexEquivSucc X x y n) f).1
    rw [← Category.assoc, ← Functor.map_comp, Iso.hom_inv_id,
      CategoryTheory.Functor.map_id, Category.id_comp]
  right_inv σ := by
    apply Subtype.ext
    change SSet.stdSimplex.map (zeroAddSuccIso n).inv ≫
        ((simplexEquivSucc X x y n)
          ((simplexEquivSucc X x y n).symm
            ⟨SSet.stdSimplex.map (zeroAddSuccIso n).hom ≫ σ.1, _⟩)).1 =
      σ.1
    rw [Equiv.apply_symm_apply]
    change SSet.stdSimplex.map (zeroAddSuccIso n).inv ≫
        (SSet.stdSimplex.map (zeroAddSuccIso n).hom ≫ σ.1) = σ.1
    rw [← Category.assoc, ← Functor.map_comp, Iso.inv_hom_id,
      CategoryTheory.Functor.map_id, Category.id_comp]

/-- The underlying `(n + 1)`-simplex of the transport
`SSet.mappingSpaceLeft.simplexEquivSuccStd` is, by definition,
precomposition with the two inverse isomorphisms. -/
lemma simplexEquivSuccStd_val (n : ℕ)
    (τ : (mappingSpaceLeft X x y).obj (op ⦋n⦌)) :
    ((simplexEquivSuccStd X x y n) τ).1 =
      SSet.stdSimplex.map (zeroAddSuccIso n).inv ≫
        (joinStdSimplexIso.{u} 0 n).inv ≫ τ.1 :=
  rfl

/-- **Face transport**: the `a`-th face of a simplex of the
left mapping space corresponds, under
`SSet.mappingSpaceLeft.simplexEquivSuccStd`, to the
`(succ a)`-th face of the transported simplex of `X`. From
`SSet.mappingSpaceLeft.map_val`, the supporting results
`SSet.joinStdSimplexIso_inv_comp_join_obj_map` (right-variable
naturality of `joinStdSimplexIso`) and
`SSet.zeroAddSuccIso_inv_comp_tensorHomOf_id_δ`. Mirror of
the supporting results `SSet.mappingSpaceRight.simplexEquivSucc_δ`. -/
theorem simplexEquivSuccStd_δ {k : ℕ}
    (σ : (mappingSpaceLeft X x y).obj (op ⦋k + 1⦌))
    (a : Fin (k + 2)) :
    ((simplexEquivSuccStd X x y k)
        ((mappingSpaceLeft X x y).δ a σ)).1 =
      stdSimplex.δ a.succ ≫
        ((simplexEquivSuccStd X x y (k + 1)) σ).1 := by
  rw [simplexEquivSuccStd_val, simplexEquivSuccStd_val]
  have hδ : ((mappingSpaceLeft X x y).δ a σ).1 =
      (join.{u}.obj (Δ[0] : SSet.{u})).map
          (SSet.stdSimplex.map (SimplexCategory.δ a)) ≫ σ.1 := rfl
  rw [hδ]
  rw [← Category.assoc ((joinStdSimplexIso.{u} 0 k).inv)
      ((join.{u}.obj (Δ[0] : SSet.{u})).map
        (SSet.stdSimplex.map (SimplexCategory.δ a))) σ.1,
    joinStdSimplexIso_inv_comp_join_obj_map
      (SimplexCategory.δ a) 0,
    Category.assoc
      (SSet.stdSimplex.map (AugmentedSimplexCategory.tensorHomOf
        (𝟙 ⦋0⦌) (SimplexCategory.δ a)))
      ((joinStdSimplexIso.{u} 0 (k + 1)).inv) σ.1,
    ← Category.assoc (SSet.stdSimplex.map (zeroAddSuccIso k).inv)
      (SSet.stdSimplex.map (AugmentedSimplexCategory.tensorHomOf
        (𝟙 ⦋0⦌) (SimplexCategory.δ a)))
      ((joinStdSimplexIso.{u} 0 (k + 1)).inv ≫ σ.1),
    ← Functor.map_comp, zeroAddSuccIso_inv_comp_tensorHomOf_id_δ a,
    Functor.map_comp, ← stdSimplex_δ_eq_map,
    Category.assoc (stdSimplex.δ a.succ)
      (SSet.stdSimplex.map (zeroAddSuccIso (k + 1)).inv)
      ((joinStdSimplexIso.{u} 0 (k + 1)).inv ≫ σ.1)]

end mappingSpaceLeft

/-! ## §3. The special right outer horn input

The one case of the horn transport that pre-fibrancy does not
literally include: a right outer horn whose `0`-th face is a
constant simplex. Its critical (last) edge lies in the `0`-th
face, hence is degenerate; for a quasicategory Joyal's special
outer horn filling therefore applies. -/

/-- A simplicial set `X` fills its special right outer horns
with constant `0`-th face: every horn
`σ₀ : Λ[n + 2, Fin.last (n + 2)] ⟶ X` whose `0`-th face
`SSet.hornFaceZero σ₀ _` is a constant simplex extends to
`Δ[n + 2]`. This is the single input of Remark 3.3 not
supplied by `SSet.IsPreFibrant` (Definition 3.1): that every
pre-fibrant simplicial set has this property is
`SSet.hasSpecialRightHornFillingWithConstantZeroFace_of_isPreFibrant`
(`PreFibrantSpecialHorn.lean`,
discharging the additional comparison obligation); every quasicategory
has it, by
`SSet.hasSpecialRightHornFillingWithConstantZeroFace_of_quasicategory`
below. -/
def HasSpecialRightHornFillingWithConstantZeroFace
    (X : SSet.{u}) : Prop :=
  ∀ ⦃n : ℕ⦄ (σ₀ : (Λ[n + 2, Fin.last (n + 2)] : SSet.{u}) ⟶ X),
    IsConstantSimplex
        (hornFaceZero σ₀
          (show (0 : Fin (n + 3)) ≠ Fin.last (n + 2)
            from by simp [Fin.ext_iff])) →
      ∃ σ : (Δ[n + 2] : SSet.{u}) ⟶ X,
        σ₀ = Λ[n + 2, Fin.last (n + 2)].ι ≫ σ

/-- Constant simplices are preserved under simplicial
operators: any face or degeneracy of `s₀ⁿ(v)` is `s₀ᵐ(v)`. -/
lemma map_constSimplex {X : SSet.{u}} {m n : ℕ} (φ : ⦋m⦌ ⟶ ⦋n⦌)
    (v : X _⦋0⦌) :
    X.map φ.op (constSimplex X n v) = constSimplex X m v := by
  have h : ((SimplexCategory.const ⦋n⦌ ⦋0⦌ 0).op ≫ φ.op) =
      (SimplexCategory.const ⦋m⦌ ⦋0⦌ 0).op :=
    congrArg Opposite.op (Subsingleton.elim _
      (SimplexCategory.const ⦋m⦌ ⦋0⦌ 0))
  calc X.map φ.op (constSimplex X n v)
      = X.map ((SimplexCategory.const ⦋n⦌ ⦋0⦌ 0).op ≫ φ.op) v := by
        rw [X.map_comp]; rfl
    _ = constSimplex X m v := by rw [h]; rfl

namespace mappingSpaceLeft

/-- The `1`-simplex of `Δ[n + 2]` spanning the last two
vertices factors through the back face: `δ₀ ∘ (last edge of
Δ[n + 1]) = last edge of Δ[n + 2]`, as simplex-category homs.
Mirror of `SSet.mappingSpaceRight.edge01_comp_δ_last`
(the supporting results). -/
lemma edgeLast_comp_δ_zero (n : ℕ) :
    (stdSimplex.edge.{u} (n + 1) ⟨n, by omega⟩ (Fin.last (n + 1))
        (by simp [Fin.le_def])).down ≫
        SimplexCategory.δ (0 : Fin (n + 3)) =
      (stdSimplex.edge.{u} (n + 2) ⟨n + 1, by omega⟩
        (Fin.last (n + 2)) (by simp [Fin.le_def])).down := by
  ext a : 3
  fin_cases a <;>
    simp [SimplexCategory.δ, stdSimplex.coe_edge_down_toOrderHom]

end mappingSpaceLeft

/-- The critical (last) edge of a right outer horn whose
`0`-th face is constant is an equivalence: the edge lies in
the `0`-th face (`SSet.mappingSpaceLeft.edgeLast_comp_δ_zero`),
which is the constant simplex at some vertex `v`, so the edge
is the degenerate identity edge `X.σ 0 v`. Mirror of the
critical-edge computation in the supporting results proof of
`SSet.kanComplex_mappingSpaceRight`. -/
theorem rightHornEdge_isEquivalence_of_isConstant_hornFaceZero
    {X : SSet.{u}} {n : ℕ}
    (σ₀ : (Λ[n + 2, Fin.last (n + 2)] : SSet.{u}) ⟶ X)
    (hconst : IsConstantSimplex
      (hornFaceZero σ₀
        (show (0 : Fin (n + 3)) ≠ Fin.last (n + 2)
          from by simp [Fin.ext_iff]))) :
    (rightHornEdge σ₀).IsEquivalence := by
  obtain ⟨v, hv⟩ := hconst
  have hed : (rightHornEdge σ₀).edge = X.σ 0 v := by
    change σ₀.app (op ⦋1⦌) (rightHornEdgeSimplex.{u} n) = X.σ 0 v
    have hface : rightHornEdgeSimplex.{u} n =
        (Λ[n + 2, Fin.last (n + 2)] :
            Subcomplex (Δ[n + 2] : SSet.{u})).toSSet.map
          ((stdSimplex.edge.{u} (n + 1) ⟨n, by omega⟩
              (Fin.last (n + 1)) (by simp [Fin.le_def])).down).op
          (horn.face (Fin.last (n + 2)) 0
            (by simp [Fin.ext_iff])) := by
      have hL : (rightHornEdgeSimplex.{u} n).1 =
          stdSimplex.edge.{u} (n + 2) ⟨n + 1, by omega⟩
            (Fin.last (n + 2)) (by simp [Fin.le_def]) :=
        rfl
      have hfaceval : (horn.face (Fin.last (n + 2)) 0
            (by simp [Fin.ext_iff])).1 =
          yonedaEquiv (stdSimplex.δ (0 : Fin (n + 3))) := by
        have e1 : horn.face (Fin.last (n + 2)) 0
              (by simp [Fin.ext_iff]) =
            yonedaEquiv (horn.ι (Fin.last (n + 2)) 0
              (by simp [Fin.ext_iff])) :=
          (horn.yonedaEquiv_ι _ _ _).symm
        rw [e1]
        change (Λ[n + 2, Fin.last (n + 2)] :
              Subcomplex (Δ[n + 2] : SSet.{u})).ι.app _
            (yonedaEquiv (horn.ι (Fin.last (n + 2)) 0
              (by simp [Fin.ext_iff]))) = _
        rw [← yonedaEquiv_comp]
        exact congrArg yonedaEquiv (horn.ι_ι _ _ _)
      have hR : ((Λ[n + 2, Fin.last (n + 2)] :
              Subcomplex (Δ[n + 2] : SSet.{u})).toSSet.map
            ((stdSimplex.edge.{u} (n + 1) ⟨n, by omega⟩
                (Fin.last (n + 1)) (by simp [Fin.le_def])).down).op
            (horn.face (Fin.last (n + 2)) 0
              (by simp [Fin.ext_iff]))).1 =
          stdSimplex.edge.{u} (n + 2) ⟨n + 1, by omega⟩
            (Fin.last (n + 2)) (by simp [Fin.le_def]) := by
        change (Δ[n + 2] : SSet.{u}).map
            ((stdSimplex.edge.{u} (n + 1) ⟨n, by omega⟩
                (Fin.last (n + 1)) (by simp [Fin.le_def])).down).op
            (horn.face (Fin.last (n + 2)) 0
              (by simp [Fin.ext_iff])).1 = _
        have hmap : (Δ[n + 2] : SSet.{u}).map
              ((stdSimplex.edge.{u} (n + 1) ⟨n, by omega⟩
                  (Fin.last (n + 1))
                    (by simp [Fin.le_def])).down).op
              (yonedaEquiv (stdSimplex.δ (0 : Fin (n + 3)))) =
            ULift.up
              ((stdSimplex.edge.{u} (n + 1) ⟨n, by omega⟩
                    (Fin.last (n + 1))
                      (by simp [Fin.le_def])).down ≫
                  SimplexCategory.δ (0 : Fin (n + 3))) :=
          rfl
        rw [hfaceval, hmap, mappingSpaceLeft.edgeLast_comp_δ_zero]
        exact rfl
      exact Subtype.ext (hL.trans hR.symm)
    have hnat : σ₀.app (op ⦋1⦌) (rightHornEdgeSimplex.{u} n) =
        X.map ((stdSimplex.edge.{u} (n + 1) ⟨n, by omega⟩
              (Fin.last (n + 1)) (by simp [Fin.le_def])).down).op
          (σ₀.app (op ⦋n + 1⦌)
            (horn.face (Fin.last (n + 2)) 0
              (by simp [Fin.ext_iff]))) := by
      rw [hface]
      have hcongr := types_congr_hom
        (σ₀.naturality
          (op (stdSimplex.edge.{u} (n + 1) ⟨n, by omega⟩
            (Fin.last (n + 1)) (by simp [Fin.le_def])).down))
        (horn.face (Fin.last (n + 2)) 0 (by simp [Fin.ext_iff]))
      simp only [types_comp_apply] at hcongr
      exact hcongr
    have hσface : σ₀.app (op ⦋n + 1⦌)
          (horn.face (Fin.last (n + 2)) 0
            (by simp [Fin.ext_iff])) =
        constSimplex X (n + 1) v :=
      hv
    rw [hnat, hσface, map_constSimplex, constSimplex_succ,
      constSimplex_zero]
  have hid : (Edge.id v).edge = (rightHornEdge σ₀).edge :=
    hed.symm
  exact (Edge.isEquivalence_iff_of_edge_eq hid).mp
    (Edge.isEquivalence_id v)

/-- Every quasicategory fills its special right outer horns
with constant `0`-th face: the critical edge is degenerate
(`SSet.rightHornEdge_isEquivalence_of_isConstant_hornFaceZero`),
so Joyal's special outer horn filling
(`SSet.hasSpecialOuterHornFilling_of_quasicategory`) applies. -/
theorem
    hasSpecialRightHornFillingWithConstantZeroFace_of_quasicategory
    (X : SSet.{u}) [Quasicategory X] :
    HasSpecialRightHornFillingWithConstantZeroFace X := by
  intro n σ₀ hconst
  exact (hasSpecialOuterHornFilling_of_quasicategory X).right σ₀
    (rightHornEdge_isEquivalence_of_isConstant_hornFaceZero σ₀
      hconst)

/-! ## §4. The horn transport (Remark 3.3)

Mirror of the supporting results `SSet.kanComplex_mappingSpaceRight`:
a horn in `Homᴸ` plus the constant back face is a horn in `X`
with constant `0`-th face, shifted by one index; it is inner
unless the original horn was right outer, in which case it is
the special right outer horn of §3. -/

/-- **Remark 3.3, modulo the special right outer horn input**:
if `X` is pre-fibrant (Stevenson, Definition 3.1) and fills
its special right outer horns with constant `0`-th face
(`SSet.HasSpecialRightHornFillingWithConstantZeroFace`,
proved for pre-fibrant `X` in `PreFibrantSpecialHorn.lean`),
then every left mapping space `Homᴸ_X(x, y)` is a Kan complex.
The proof is the horn transport of the file header:
one-dimensional horns are filled by degeneracies; in higher
dimensions a horn `Λ[n + 2, i]` in `Homᴸ_X(x, y)` together
with the constant back face at `y` is a horn
`Λ[n + 3, i.succ]` in `X` with constant `0`-th face, which is
inner for `i ≠ last` (filled by pre-fibrancy,
Definition 3.1(ii)) and a special right outer horn for
`i = last` (filled by the named hypothesis). -/
theorem kanComplex_mappingSpaceLeft_of_isPreFibrant_of_special
    (X : SSet.{u}) [IsPreFibrant X]
    (hspec : HasSpecialRightHornFillingWithConstantZeroFace X)
    (x y : (Δ[0] : SSet.{u}) ⟶ X) :
    KanComplex (mappingSpaceLeft X x y) := by
  rw [KanComplex.iff]
  intro n i f hf
  obtain _ | n := n
  · -- One-dimensional horns: fill by the degenerate edge.
    obtain ⟨j₀, hj₀⟩ : ∃ j : Fin 2, j ≠ i := by
      by_cases hi : i = 0
      · exact ⟨1, by simp [hi]⟩
      · exact ⟨0, Ne.symm hi⟩
    have hδσ : stdSimplex.δ j₀ ≫ stdSimplex.σ (0 : Fin 1) =
        𝟙 (Δ[0] : SSet.{u}) := by
      have hσ : (stdSimplex.σ (0 : Fin 1) :
            (Δ[1] : SSet.{u}) ⟶ Δ[0]) =
          SSet.stdSimplex.map (SimplexCategory.σ (0 : Fin 1)) := rfl
      rw [stdSimplex_δ_eq_map, hσ, ← CategoryTheory.Functor.map_comp]
      have hcomp : SimplexCategory.δ j₀ ≫
          SimplexCategory.σ (0 : Fin 1) = 𝟙 ⦋0⦌ := by
        fin_cases j₀
        · exact SimplexCategory.δ_comp_σ_self
        · exact SimplexCategory.δ_comp_σ_succ
      rw [hcomp, CategoryTheory.Functor.map_id]
    refine ⟨stdSimplex.σ 0 ≫ f j₀ hj₀, fun j hj ↦ ?_⟩
    have hji : j = j₀ := by
      have h1 : j.val < 2 := j.is_lt
      have h2 : j₀.val < 2 := j₀.is_lt
      have h3 : i.val < 2 := i.is_lt
      apply Fin.ext
      simp only [ne_eq, Fin.ext_iff] at hj hj₀
      omega
    subst hji
    rw [← Category.assoc, hδσ, Category.id_comp]
  · -- Higher-dimensional horns: transport to `X`.
    -- The transported faces `s j : Δ[n + 2] ⟶ X`.
    set s : ∀ (j : Fin (n + 3)) (_ : j ≠ i), (Δ[n + 2] : SSet.{u}) ⟶ X :=
      fun j hj ↦
        ((mappingSpaceLeft.simplexEquivSuccStd X x y (n + 1))
          (yonedaEquiv (f j hj))).1 with hs
    have hsback : ∀ (j : Fin (n + 3)) (hj : j ≠ i),
        stdSimplex.δ (0 : Fin (n + 3)) ≫ s j hj =
          toDeltaZero (Δ[n + 1] : SSet.{u}) ≫ y :=
      fun j hj ↦
        ((mappingSpaceLeft.simplexEquivSuccStd X x y (n + 1))
          (yonedaEquiv (f j hj))).2.2
    have hsvert : ∀ (j : Fin (n + 3)) (hj : j ≠ i),
        SSet.stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋n + 2⦌ 0) ≫
            s j hj = x :=
      fun j hj ↦
        ((mappingSpaceLeft.simplexEquivSuccStd X x y (n + 1))
          (yonedaEquiv (f j hj))).2.1
    -- The horn in `X`: add the constant back face as face `0`.
    set g : ∀ (k : Fin (n + 4)) (_ : k ≠ i.succ),
        (Δ[n + 2] : SSet.{u}) ⟶ X := fun k hk ↦
      if hk0 : k = 0 then toDeltaZero Δ[n + 2] ≫ y
      else s (k.pred hk0)
        (fun h ↦ hk (by rw [← Fin.succ_pred k hk0, h])) with hg
    have hg_zero : ∀ (h : (0 : Fin (n + 4)) ≠ i.succ),
        g 0 h = toDeltaZero (Δ[n + 2] : SSet.{u}) ≫ y := by
      intro h
      exact dite_eq_left rfl
    have hg_succ : ∀ (j : Fin (n + 3)) (hj : j ≠ i)
        (h : j.succ ≠ i.succ), g j.succ h = s j hj := by
      intro j hj h
      exact dite_eq_right (Fin.succ_ne_zero j)
    have hcompat : horn.IsCompatible g := by
      rw [horn.isCompatible_iff]
      intro j k hj hk hjk
      by_cases hj0 : j = 0
      · -- Compatibility with the constant back face.
        subst hj0
        obtain ⟨k', rfl⟩ := k.eq_succ_of_ne_zero
          (Fin.ne_zero_of_lt hjk)
        have hk' : k' ≠ i := fun h ↦ hk (by rw [h])
        have htd : stdSimplex.δ
              ((k'.succ).pred (Fin.ne_zero_of_lt hjk)) ≫
              toDeltaZero (Δ[n + 2] : SSet.{u}) =
            toDeltaZero (Δ[n + 1] : SSet.{u}) := toDeltaZero_eq _
        have e0 : (0 : Fin (n + 4)).castPred
            (Fin.ne_last_of_lt hjk) = 0 := rfl
        rw [hg_zero, hg_succ k' hk' hk, e0, hsback k' hk',
          ← Category.assoc
            (stdSimplex.δ ((k'.succ).pred (Fin.ne_zero_of_lt hjk))),
          htd]
      · -- Compatibility of two transported faces: reduce to `hf`.
        obtain ⟨j', rfl⟩ := j.eq_succ_of_ne_zero hj0
        obtain ⟨k', rfl⟩ := k.eq_succ_of_ne_zero
          (Fin.ne_zero_of_lt hjk)
        have hj' : j' ≠ i := fun h ↦ hj (by rw [h])
        have hk' : k' ≠ i := fun h ↦ hk (by rw [h])
        have hjk' : j' < k' := Fin.succ_lt_succ_iff.mp hjk
        have hδδ : ∀ (a : Fin (n + 2)) (φ : (Δ[n + 1] : SSet.{u}) ⟶
              mappingSpaceLeft X x y),
            (mappingSpaceLeft X x y).δ a (yonedaEquiv φ) =
              yonedaEquiv (stdSimplex.δ a ≫ φ) := by
          intro a φ
          have h := stdSimplex.δ_comp_yonedaEquiv_symm
            (X := mappingSpaceLeft X x y) (i := a) (x := yonedaEquiv φ)
          rw [Equiv.symm_apply_apply] at h
          calc (mappingSpaceLeft X x y).δ a (yonedaEquiv φ)
              = yonedaEquiv (yonedaEquiv.symm
                  ((mappingSpaceLeft X x y).δ a (yonedaEquiv φ))) :=
                (Equiv.apply_symm_apply _ _).symm
            _ = yonedaEquiv (stdSimplex.δ a ≫ φ) := by rw [← h]
        have hidxL : (k'.succ).pred (Fin.ne_zero_of_lt hjk) =
            (k'.pred (Fin.ne_zero_of_lt hjk')).succ := by
          rw [Fin.pred_succ, Fin.succ_pred]
        have hidxR : (j'.succ).castPred (Fin.ne_last_of_lt hjk) =
            (j'.castPred (Fin.ne_last_of_lt hjk')).succ :=
          (Fin.succ_castPred_eq_castPred_succ
            (Fin.ne_last_of_lt hjk')).symm
        have hLHS : stdSimplex.δ
              (k'.pred (Fin.ne_zero_of_lt hjk')).succ ≫ s j' hj' =
            ((mappingSpaceLeft.simplexEquivSuccStd X x y n)
              (yonedaEquiv (stdSimplex.δ
                (k'.pred (Fin.ne_zero_of_lt hjk')) ≫
                  f j' hj'))).1 := by
          rw [show s j' hj' =
              ((mappingSpaceLeft.simplexEquivSuccStd X x y (n + 1))
                (yonedaEquiv (f j' hj'))).1 from rfl,
            ← mappingSpaceLeft.simplexEquivSuccStd_δ X x y
              (yonedaEquiv (f j' hj'))
              (k'.pred (Fin.ne_zero_of_lt hjk')), hδδ]
        have hRHS : stdSimplex.δ
              (j'.castPred (Fin.ne_last_of_lt hjk')).succ ≫
              s k' hk' =
            ((mappingSpaceLeft.simplexEquivSuccStd X x y n)
              (yonedaEquiv (stdSimplex.δ
                (j'.castPred (Fin.ne_last_of_lt hjk')) ≫
                  f k' hk'))).1 := by
          rw [show s k' hk' =
              ((mappingSpaceLeft.simplexEquivSuccStd X x y (n + 1))
                (yonedaEquiv (f k' hk'))).1 from rfl,
            ← mappingSpaceLeft.simplexEquivSuccStd_δ X x y
              (yonedaEquiv (f k' hk'))
              (j'.castPred (Fin.ne_last_of_lt hjk')), hδδ]
        rw [hg_succ j' hj' hj, hg_succ k' hk' hk, hidxL, hidxR,
          hLHS, hRHS]
        exact congrArg (fun τ =>
          ((mappingSpaceLeft.simplexEquivSuccStd X x y n) τ).1)
          (congrArg yonedaEquiv (hf.δ_pred_comp j' k' hj' hk' hjk'))
    -- The `0`-th face of the transported horn is constant.
    obtain ⟨σ₀, hσ₀⟩ := hcompat.exists_desc
    have hy : y = SSet.const (yonedaEquiv y) := by
      apply yonedaEquiv.injective
      rw [yonedaEquiv_const_eq, constSimplex_zero]
    have hconst : IsConstantSimplex
        (hornFaceZero σ₀ (Ne.symm (Fin.succ_ne_zero i))) := by
      rw [hornFaceZero_eq_yonedaEquiv,
        hσ₀ 0 (Ne.symm (Fin.succ_ne_zero i)), hg_zero,
        isConstantSimplex_yonedaEquiv_iff]
      refine ⟨yonedaEquiv y, ?_⟩
      calc toDeltaZero (Δ[n + 2] : SSet.{u}) ≫ y
          = toDeltaZero (Δ[n + 2] : SSet.{u}) ≫
              SSet.const (yonedaEquiv y) :=
            congrArg (toDeltaZero (Δ[n + 2] : SSet.{u}) ≫ ·) hy
        _ = SSet.const (yonedaEquiv y) := SSet.comp_const _ _
    -- Fill the horn in `X`.
    obtain ⟨Φ, hΦ⟩ : ∃ (Φ : (Δ[n + 3] : SSet.{u}) ⟶ X),
        ∀ (k : Fin (n + 4)) (hk : k ≠ i.succ),
          stdSimplex.δ k ≫ Φ = g k hk := by
      by_cases hi : i = Fin.last (n + 2)
      · subst hi
        obtain ⟨Φ, hΦeq⟩ := hspec σ₀ hconst
        refine ⟨Φ, fun k hk ↦ ?_⟩
        calc stdSimplex.δ k ≫ Φ
            = horn.ι (Fin.last (n + 3)) k hk ≫
                ((Λ[n + 3, Fin.last (n + 3)] :
                    Subcomplex (Δ[n + 3] : SSet.{u})).ι ≫ Φ) := by
              rw [← Category.assoc, horn.ι_ι]
          _ = horn.ι (Fin.last (n + 3)) k hk ≫ σ₀ := by
              rw [show (Λ[n + 3, Fin.last (n + 3)] :
                    Subcomplex (Δ[n + 3] : SSet.{u})).ι ≫ Φ = σ₀ from
                  hΦeq.symm]
          _ = g k hk := hσ₀ k hk
      · have hn : i.succ < Fin.last (n + 3) := by
          have h2 : i.val ≠ n + 2 := fun h ↦ hi (Fin.ext h)
          have h1 : i.val < n + 3 := i.is_lt
          simp only [Fin.lt_def, Fin.val_succ, Fin.val_last]
          omega
        obtain ⟨Φ, hΦeq⟩ := IsPreFibrant.hornFillingConst σ₀
          (Fin.pos_iff_ne_zero.mpr (Fin.succ_ne_zero i)) hn hconst
        refine ⟨Φ, fun k hk ↦ ?_⟩
        calc stdSimplex.δ k ≫ Φ
            = horn.ι i.succ k hk ≫
                ((Λ[n + 3, i.succ] :
                    Subcomplex (Δ[n + 3] : SSet.{u})).ι ≫ Φ) := by
              rw [← Category.assoc, horn.ι_ι]
          _ = horn.ι i.succ k hk ≫ σ₀ := by
              rw [show (Λ[n + 3, i.succ] :
                    Subcomplex (Δ[n + 3] : SSet.{u})).ι ≫ Φ = σ₀ from
                  hΦeq.symm]
          _ = g k hk := hσ₀ k hk
    -- The filler lies in the mapping space.
    have hΦback : stdSimplex.δ (0 : Fin (n + 4)) ≫ Φ =
        toDeltaZero (Δ[n + 2] : SSet.{u}) ≫ y := by
      rw [hΦ 0 (Ne.symm (Fin.succ_ne_zero i)), hg_zero]
    have hΦvert : SSet.stdSimplex.map
          (SimplexCategory.const ⦋0⦌ ⦋n + 3⦌ 0) ≫ Φ = x := by
      obtain ⟨j₀, hj₀⟩ : ∃ j : Fin (n + 3), j ≠ i := by
        by_cases hi : i = 0
        · exact ⟨1, by simp [hi]⟩
        · exact ⟨0, Ne.symm hi⟩
      calc SSet.stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋n + 3⦌ 0) ≫ Φ
          = (SSet.stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋n + 2⦌ 0) ≫
              stdSimplex.δ j₀.succ) ≫ Φ := by
            rw [vertexZero_comp_δ_succ]
        _ = SSet.stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋n + 2⦌ 0) ≫
              (stdSimplex.δ j₀.succ ≫ Φ) :=
            Category.assoc _ _ _
        _ = SSet.stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋n + 2⦌ 0) ≫
              s j₀ hj₀ := by
            rw [hΦ j₀.succ (by
              simp only [ne_eq, Fin.succ_inj]
              exact hj₀), hg_succ j₀ hj₀]
        _ = x := hsvert j₀ hj₀
    -- Assemble the filler in the mapping space.
    refine ⟨yonedaEquiv.symm
      ((mappingSpaceLeft.simplexEquivSuccStd X x y (n + 2)).symm
        ⟨Φ, hΦvert, hΦback⟩), fun j hj ↦ ?_⟩
    rw [stdSimplex.δ_comp_yonedaEquiv_symm,
      show f j hj = yonedaEquiv.symm (yonedaEquiv (f j hj)) from
        (Equiv.symm_apply_apply _ _).symm]
    congr 1
    apply (mappingSpaceLeft.simplexEquivSuccStd X x y
      (n + 1)).injective
    apply Subtype.ext
    rw [mappingSpaceLeft.simplexEquivSuccStd_δ X x y
      ((mappingSpaceLeft.simplexEquivSuccStd X x y (n + 2)).symm
        ⟨Φ, hΦvert, hΦback⟩) j, Equiv.apply_symm_apply,
      hΦ j.succ (by
        simp only [ne_eq, Fin.succ_inj]
        exact hj), hg_succ j hj]

/-! ## §5. Consequences: Remark 3.3 in the consumed form -/

/-- **Left mapping spaces of a quasicategory are Kan
complexes**: the left analogue of the supporting results
`SSet.kanComplex_mappingSpaceRight`, via the horn transport
of §4 with the special right outer horn input supplied by
Joyal's special outer horn filling (§3). -/
theorem kanComplex_mappingSpaceLeft (X : SSet.{u})
    [Quasicategory X] (x y : (Δ[0] : SSet.{u}) ⟶ X) :
    KanComplex (mappingSpaceLeft X x y) :=
  kanComplex_mappingSpaceLeft_of_isPreFibrant_of_special X
    (hasSpecialRightHornFillingWithConstantZeroFace_of_quasicategory
      X) x y

/-- Instance form of `SSet.kanComplex_mappingSpaceLeft`
(mirror of the instance for right mapping spaces in
the supporting results). -/
instance (X : SSet.{u}) [Quasicategory X]
    (x y : (Δ[0] : SSet.{u}) ⟶ X) :
    KanComplex (mappingSpaceLeft X x y) :=
  kanComplex_mappingSpaceLeft X x y

/-- **Remark 3.3 for quasicategories**, in the exact predicate
form `SSet.LeftMappingSpacesKan` consumed by
`DescentProp412.lean` (the hypothesis
`hKanQC : ∀ A, Quasicategory A → LeftMappingSpacesKan A`
there). -/
theorem leftMappingSpacesKan_of_quasicategory (X : SSet.{u})
    [Quasicategory X] : LeftMappingSpacesKan X :=
  fun a b ↦ kanComplex_mappingSpaceLeft X a b

/-- **Remark 3.3 for pre-fibrant simplicial sets, modulo the
named special right outer horn input**
(proved in `PreFibrantSpecialHorn.lean`): if `X` is pre-fibrant and
fills its special right outer horns with constant `0`-th
face, then `SSet.LeftMappingSpacesKan X` holds, discharging
the additional comparison obligation of
`DescentProp412.lean` modulo that single
input (see `SSet.leftMappingSpacesKan_of_isPreFibrant` for the
unconditional form). -/
theorem leftMappingSpacesKan_of_isPreFibrant_of_special
    (X : SSet.{u}) [IsPreFibrant X]
    (hspec : HasSpecialRightHornFillingWithConstantZeroFace X) :
    LeftMappingSpacesKan X :=
  fun a b ↦
    kanComplex_mappingSpaceLeft_of_isPreFibrant_of_special X hspec
      a b

end SSet

end
