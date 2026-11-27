/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.HornDescent
public import MathlibExt.AlgebraicTopology.Quasicategory.CoreKan
public import MathlibExt.AlgebraicTopology.Quasicategory.SpecialOuterHornGeneral
public import MathlibExt.AlgebraicTopology.SimplicialSet.JoinNaturality

/-!
# Kan left mapping spaces from simplicial horn conditions

An `n`-simplex of the left mapping space `Homᴸ_X(x,y)` is an `(n + 1)`-simplex
of `X` with zero vertex `x` and zero face constant at `y`. Its face indexed by `j`
corresponds to face `j + 1` of that simplex.

If `X` is prefibrant and fills the special right outer horns with constant zero face,
this description transports every mapping-space horn to a fillable horn in `X`, so
all left mapping spaces are Kan complexes. For a quasicategory, the special right
outer horn condition follows because its critical edge is degenerate.

See Stevenson, Notes on the Joyal model structure, arXiv:1810.05233v1, §§2.4 and 3.1,
and Lurie, Higher Topos Theory, §§1.2.2 and 1.2.8–1.2.9.
-/

@[expose] public section

noncomputable section

open CategoryTheory MonoidalCategory Limits Opposite
open scoped Simplicial
open scoped CategoryTheory.MonoidalCategory.DayFunctor

universe u

namespace SSet

/-!
## Back face under the standard join identification

The right join inclusion identifies with the back face of the standard simplex.
After the identification `Δ[0] ⋆ Δ[n] ≅ Δ[n + 1]`, this face is `d₀`.
-/

/--
The transported back inclusion equals the standard-simplex map induced by the
right inclusion in the augmented simplex join.
-/
theorem backInclusion_eq (n : ℕ) :
    backInclusion.{u} n =
      SSet.stdSimplex.map (AugmentedSimplexCategory.inr' ⦋0⦌ ⦋n⦌) :=
  joinInr_comp_joinStdSimplexIso_hom 0 n

/--
After the successor-simplex identification, the transported back inclusion is
`d₀ : Δ[n] → Δ[n + 1]`.
-/
theorem backInclusionSucc_eq (n : ℕ) :
    backInclusionSucc.{u} n = stdSimplex.δ (0 : Fin (n + 2)) := by
  rw [backInclusionSucc, backInclusion_eq, ← Functor.map_comp,
    inr'_zero_comp_zeroAddSuccIso_hom]
  exact (stdSimplex_δ_eq_map _).symm

/-!
## Standard simplices of left mapping spaces

The standard representation of a left mapping-space simplex has vertex zero `x`
and back face constant at `y`. Mapping-space face `j` is standard-simplex face
`j + 1`, preserving vertex zero and the constant back-face condition.
-/

/--
The zero vertex inclusion followed by a face that does not omit vertex zero is
the zero vertex inclusion in the next dimension.
-/
lemma vertexZero_comp_δ_succ {n : ℕ} (j : Fin (n + 2)) :
    SSet.stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋n + 1⦌ 0) ≫
        stdSimplex.δ j.succ =
      SSet.stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋n + 2⦌ 0) := by
  rw [stdSimplex_δ_eq_map, ← Functor.map_comp]
  congr 1

namespace mappingSpaceLeft

variable (X : SSet.{u}) (x y : (Δ[0] : SSet.{u}) ⟶ X)

/--
The equivalence between degree-`n` left mapping-space simplices and maps
`σ : Δ[n + 1] → X` whose zero vertex is `x` and zero face is the constant
`n`-simplex at `y`.
-/
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

/--
The standard simplex of a left mapping-space simplex is its join map precomposed
with the inverse join and successor-simplex identifications.
-/
lemma simplexEquivSuccStd_val (n : ℕ)
    (τ : (mappingSpaceLeft X x y).obj (op ⦋n⦌)) :
    ((simplexEquivSuccStd X x y n) τ).1 =
      SSet.stdSimplex.map (zeroAddSuccIso n).inv ≫
        (joinStdSimplexIso.{u} 0 n).inv ≫ τ.1 :=
  rfl

/--
Under the standard-coordinate equivalence, face `a` of a mapping-space simplex
is face `a + 1` of its representing simplex in `X`.
-/
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

/-!
## Right outer horns with constant zero face

In a right outer horn with constant zero face, the edge between the last two
vertices lies in that constant face and is degenerate. In a quasicategory the
special outer-horn filling property therefore gives a filler.
-/

/--
The condition that every right outer horn `Λ[n + 2,n + 2] → X` whose zero face
is constant extends to a simplex `Δ[n + 2] → X`.
-/
def HasSpecialRightHornFillingWithConstantZeroFace
    (X : SSet.{u}) : Prop :=
  ∀ ⦃n : ℕ⦄ (σ₀ : (Λ[n + 2, Fin.last (n + 2)] : SSet.{u}) ⟶ X),
    IsConstantSimplex
        (hornFaceZero σ₀
          (show (0 : Fin (n + 3)) ≠ Fin.last (n + 2)
            from by simp [Fin.ext_iff])) →
      ∃ σ : (Δ[n + 2] : SSet.{u}) ⟶ X,
        σ₀ = Λ[n + 2, Fin.last (n + 2)].ι ≫ σ

/--
Applying any simplicial operator to the constant simplex at a vertex gives the
constant simplex at that same vertex in the resulting degree.
-/
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

/--
The edge between the last two vertices of `Δ[n + 2]` is the last edge of
`Δ[n + 1]` followed by the back-face inclusion `d₀`.
-/
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

/--
The critical last edge of a right outer horn with constant zero face is an
equivalence edge, because it is degenerate within that face.
-/
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

/--
Every quasicategory fills right outer horns with constant zero face.
-/
theorem
    hasSpecialRightHornFillingWithConstantZeroFace_of_quasicategory
    (X : SSet.{u}) [Quasicategory X] :
    HasSpecialRightHornFillingWithConstantZeroFace X := by
  intro n σ₀ hconst
  exact (hasSpecialOuterHornFilling_of_quasicategory X).right σ₀
    (rightHornEdge_isEquivalence_of_isConstant_hornFaceZero σ₀
      hconst)

/-!
## Horn lifting in left mapping spaces

A positive-dimensional horn of a left mapping space, together with its constant
back face, determines a horn in `X` whose missing-face index is shifted by one.
The inner cases use prefibrancy, and the last outer case uses the special right
outer horn condition. One-dimensional mapping-space horns use degenerate edges.
-/

/--
If `X` is prefibrant and fills special right outer horns with constant zero face,
then `Homᴸ_X(x,y)` is a Kan complex for every pair of vertices.
-/
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

/-!
## Kan conditions on the family of left mapping spaces

For a quasicategory, every left mapping space is Kan. For a prefibrant simplicial
set with the special right outer horn condition, the same conclusion holds, both
for individual vertex pairs and for the predicate quantifying over all pairs.
-/

/--
Every left mapping space of a quasicategory is a Kan complex.
-/
theorem kanComplex_mappingSpaceLeft (X : SSet.{u})
    [Quasicategory X] (x y : (Δ[0] : SSet.{u}) ⟶ X) :
    KanComplex (mappingSpaceLeft X x y) :=
  kanComplex_mappingSpaceLeft_of_isPreFibrant_of_special X
    (hasSpecialRightHornFillingWithConstantZeroFace_of_quasicategory
      X) x y

/-- Instance form of `SSet.kanComplex_mappingSpaceLeft`
(mirror of the instance for right mapping spaces in
packet T42). -/
instance (X : SSet.{u}) [Quasicategory X]
    (x y : (Δ[0] : SSet.{u}) ⟶ X) :
    KanComplex (mappingSpaceLeft X x y) :=
  kanComplex_mappingSpaceLeft X x y

/--
A quasicategory satisfies the predicate that all its left mapping spaces are
Kan complexes.
-/
theorem leftMappingSpacesKan_of_quasicategory (X : SSet.{u})
    [Quasicategory X] : LeftMappingSpacesKan X :=
  fun a b ↦ kanComplex_mappingSpaceLeft X a b

/--
A prefibrant simplicial set filling special right outer horns with constant zero
face has Kan left mapping spaces for all vertex pairs.
-/
theorem leftMappingSpacesKan_of_isPreFibrant_of_special
    (X : SSet.{u}) [IsPreFibrant X]
    (hspec : HasSpecialRightHornFillingWithConstantZeroFace X) :
    LeftMappingSpacesKan X :=
  fun a b ↦
    kanComplex_mappingSpaceLeft_of_isPreFibrant_of_special X hspec
      a b

end SSet

end
