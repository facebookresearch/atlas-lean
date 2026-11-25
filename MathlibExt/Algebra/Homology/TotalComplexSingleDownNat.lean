/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.Algebra.Homology.Additive
public import MathlibExt.Algebra.Homology.PartialTotalBasic

/-!
# Totals of componentwise degree-zero chain complexes

Let C be preadditive with a zero object and finite coproducts. For a nonnegative chain complex
L, place each term L_p in inner degree zero to form a bicomplex B. The diagonal direct-sum total
of B is canonically isomorphic to L. In degree n the comparison selects the sole possibly
nonzero summand B_{n,0}, and its inverse is that summand's inclusion.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasFiniteCoproducts C]

/-- Let C be preadditive with a zero object and finite coproducts. For a natural-number-indexed
chain complex L, let B be the bicomplex obtained by putting each L_p in inner degree zero. There
is a canonical chain-complex isomorphism Tot(B) ≅ L. Its forward map selects B_{n,0} in total
degree n, and its inverse is the inclusion of this summand through the degree-zero
identification. -/
noncomputable def single₀MapTotalIso (L : ChainComplex C ℕ) :
    HomologicalComplex₂.total
      (((ChainComplex.single₀ C).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj L :
          HomologicalComplex₂ C (ComplexShape.down ℕ)
            (ComplexShape.down ℕ)) (ComplexShape.down ℕ) ≅ L := by
  let B : HomologicalComplex₂ C (ComplexShape.down ℕ)
      (ComplexShape.down ℕ) :=
    ((ChainComplex.single₀ C).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj L
  let homComponent : ∀ (n j a : ℕ) (_ : j + a = n),
      ((B.X j).X a ⟶ L.X n) := fun n j a h ↦ by
    if ha : a = 0 then
      subst a
      subst n
      exact (HomologicalComplex.singleObjXSelf
        (ComplexShape.down ℕ) 0 (L.X j)).hom
    else
      exact 0
  let homX : ∀ n : ℕ, (B.total (ComplexShape.down ℕ)).X n ⟶
      L.X n := fun n ↦ B.totalDesc
        (fun j a h ↦ homComponent n j a h)
  let invX : ∀ n : ℕ, L.X n ⟶
      (B.total (ComplexShape.down ℕ)).X n := fun n ↦
    (HomologicalComplex.singleObjXSelf
        (ComplexShape.down ℕ) 0 (L.X n)).inv ≫
      B.ιTotal (ComplexShape.down ℕ) n 0 n rfl
  let e : ∀ n : ℕ, (B.total (ComplexShape.down ℕ)).X n ≅
      L.X n := fun n ↦
    { hom := homX n
      inv := invX n
      hom_inv_id := by
        apply HomologicalComplex₂.total.hom_ext
        intro j a h
        cases a with
        | zero =>
            have hj : j = n := h
            subst j
            have hh : h = rfl := Subsingleton.elim _ _
            cases hh
            dsimp only [homX, invX]
            rw [← Category.assoc, HomologicalComplex₂.ι_totalDesc]
            dsimp only [homComponent]
            rw [dite_eq_left rfl]
            simp only [Iso.hom_inv_id_assoc, Category.comp_id]
        | succ a =>
            exact (HomologicalComplex.isZero_single_obj_X
              (ComplexShape.down ℕ) 0 (L.X j) (a + 1)
                (Nat.succ_ne_zero a)).eq_of_src _ _
      inv_hom_id := by
        dsimp only [homX, invX]
        rw [Category.assoc, HomologicalComplex₂.ι_totalDesc]
        dsimp only [homComponent]
        exact (HomologicalComplex.singleObjXSelf
          (ComplexShape.down ℕ) 0 (L.X n)).inv_hom_id }
  exact HomologicalComplex.Hom.isoOfComponents e (fun n n' hnn' ↦ by
    apply HomologicalComplex₂.total.hom_ext
    intro j a h
    cases a with
    | zero =>
        have hj : j = n := h
        subst j
        dsimp only [e, homX]
        rw [← Category.assoc, HomologicalComplex₂.ι_totalDesc]
        change (HomologicalComplex.singleObjXSelf
            (ComplexShape.down ℕ) 0 (L.X n)).hom ≫ L.d n n' = _
        conv_rhs => rw [← Category.assoc]
        rw [HomologicalComplex₂.total_d, Preadditive.comp_add,
          HomologicalComplex₂.ι_D₁,
          HomologicalComplex₂.ι_D₂,
          Preadditive.add_comp]
        rw [B.d₂_eq_zero (ComplexShape.down ℕ) n 0 n' (by simp)]
        simp only [zero_comp, add_zero]
        rw [B.d₁_eq (ComplexShape.down ℕ) hnn' 0 n'
          rfl]
        have heps : ComplexShape.ε₁ (ComplexShape.down ℕ)
            (ComplexShape.down ℕ) (ComplexShape.down ℕ) (n, 0) = 1 := rfl
        rw [heps, one_smul, Category.assoc,
          HomologicalComplex₂.ι_totalDesc]
        change (HomologicalComplex.singleObjXSelf
            (ComplexShape.down ℕ) 0 (L.X n)).hom ≫ L.d n n' =
          (B.d n n').f 0 ≫
            homComponent n' n' 0 rfl
        dsimp only [homComponent]
        rw [dite_eq_left rfl]
        change (HomologicalComplex.singleObjXSelf
            (ComplexShape.down ℕ) 0 (L.X n)).hom ≫ L.d n n' =
          ((ChainComplex.single₀ C).map (L.d n n')).f 0 ≫
            (HomologicalComplex.singleObjXSelf
              (ComplexShape.down ℕ) 0 (L.X n')).hom
        simp only [ChainComplex.single₀_map_f_zero,
          ChainComplex.single₀ObjXSelf, Iso.refl_hom]
        change 𝟙 (L.X n) ≫ L.d n n' =
          L.d n n' ≫ 𝟙 (L.X n')
        rw [Category.id_comp, Category.comp_id]
    | succ a =>
        exact (HomologicalComplex.isZero_single_obj_X
          (ComplexShape.down ℕ) 0 (L.X j) (a + 1)
            (Nat.succ_ne_zero a)).eq_of_src _ _)

/-- Let C be preadditive with a zero object and finite coproducts. For a nonnegative chain complex L
and j ∈ ℕ, let B be its componentwise degree-zero bicomplex and e : Tot(B) ≅ L the canonical
isomorphism. Then the summand inclusion ι_{j,0} followed by e.hom_j is the identity of L_j. -/
@[reassoc]
theorem ιTotal_comp_single₀MapTotalIso_hom
    (L : ChainComplex C ℕ) (j : ℕ) :
    HomologicalComplex₂.ιTotal
        (((ChainComplex.single₀ C).mapHomologicalComplex
          (ComplexShape.down ℕ)).obj L :
            HomologicalComplex₂ C (ComplexShape.down ℕ)
              (ComplexShape.down ℕ))
        (ComplexShape.down ℕ) j 0 j (Nat.add_zero j) ≫
      (single₀MapTotalIso L).hom.f j = 𝟙 (L.X j) := by
  unfold single₀MapTotalIso
  dsimp only [HomologicalComplex.Hom.isoOfComponents_hom_f]
  rw [HomologicalComplex₂.ι_totalDesc]
  rfl

end HomologicalComplex₂

end
