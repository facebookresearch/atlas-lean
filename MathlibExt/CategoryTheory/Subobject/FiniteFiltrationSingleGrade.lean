/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/

module

public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Subobject.Lattice

/-!
# A finite filtration with one possible graded degree

Let F be a decreasing integer-indexed subobject filtration of an object B
in an abelian category, with F⁰=B and F^{N+1}=0 for N∈ℕ.
If every graded quotient Fᵖ/Fᵖ⁺¹ for p≠n is zero, then Fⁿ=B and
Fⁿ⁺¹=0, so the n-th graded quotient is canonically B.

The comparison sends the quotient projection Fⁿ → GrⁿF to the inclusion
Fⁿ↪B. It is natural for a commuting square of the two filtration steps
at n+1 and n whose degree-n map is compatible with the ambient object map.
The integer n is arbitrary.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace CategoryTheory.Subobject

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {B : C}

private theorem eq_of_isZero_cokernel_ofLE
    (P Q : Subobject B) (h : P ≤ Q) (hz : IsZero (cokernel (Subobject.ofLE P Q h))) :
    P = Q := by
  letI : Epi (Subobject.ofLE P Q h) := Preadditive.epi_of_isZero_cokernel _ hz
  letI : IsIso (Subobject.ofLE P Q h) := isIso_of_mono_of_epi _
  exact Subobject.eq_of_comm (asIso (Subobject.ofLE P Q h)) (Subobject.ofLE_arrow h)

/-- Let C be abelian, B an object and F:ℤ → Subobject(B) decreasing.
For N∈ℕ assume F⁰=B and F^{N+1}=0, and fix n∈ℤ.
Assume GrᵖF=Coker(Fᵖ⁺¹↪Fᵖ) is zero for every integer p≠n.

The two endpoints of the possibly surviving graded degree are Fⁿ=B and Fⁿ⁺¹=0. -/
theorem finiteFiltration_singleGrade_endpoints
    (F : ℤ → Subobject B) (hF : Antitone F) (N : ℕ)
    (h₀ : F 0 = ⊤) (hN : F ((N : ℤ) + 1) = ⊥)
    (n : ℤ)
    (hz : ∀ p : ℤ, p ≠ n →
      IsZero (cokernel (Subobject.ofLE (F (p + 1)) (F p) (hF (by omega))))) :
    F n = ⊤ ∧ F (n + 1) = ⊥ := by
  constructor
  · by_cases hn : n ≤ 0
    · apply top_le_iff.mp
      rw [← h₀]
      exact hF hn
    · have h : ∀ k : ℕ, (k : ℤ) ≤ n → F (k : ℤ) = ⊤ := by
        intro k
        induction k with
        | zero => intro _; exact h₀
        | succ k ih =>
          intro hk
          have heq : F ((k : ℤ) + 1) = F (k : ℤ) :=
            eq_of_isZero_cokernel_ofLE _ _ (hF (by omega)) (hz (k : ℤ) (by omega))
          calc
            F ((k + 1 : ℕ) : ℤ) = F (k : ℤ) := by
              simpa only [Nat.cast_add, Nat.cast_one] using heq
            _ = ⊤ := ih (by omega)
      have heq : (n.toNat : ℤ) = n := by omega
      simpa only [heq] using h n.toNat (by omega)
  · by_cases hn : (N : ℤ) ≤ n
    · apply le_bot_iff.mp
      rw [← hN]
      exact hF (by omega)
    · have h : ∀ k : ℕ, n + 1 ≤ (N : ℤ) + 1 - (k : ℤ) →
          F ((N : ℤ) + 1 - (k : ℤ)) = ⊥ := by
        intro k
        induction k with
        | zero => intro _; simpa only [Nat.cast_zero, sub_zero] using hN
        | succ k ih =>
          intro hk
          let p : ℤ := (N : ℤ) + 1 - ((k + 1 : ℕ) : ℤ)
          have heq : F (p + 1) = F p :=
            eq_of_isZero_cokernel_ofLE _ _ (hF (by omega)) (hz p (by dsimp [p]; omega))
          have hp : p + 1 = (N : ℤ) + 1 - (k : ℤ) := by dsimp [p]; omega
          calc
            F ((N : ℤ) + 1 - ((k + 1 : ℕ) : ℤ)) = F ((N : ℤ) + 1 - (k : ℤ)) := by
              simpa only [hp] using heq.symm
            _ = ⊥ := ih (by omega)
      have heq : (N : ℤ) + 1 - (((N : ℤ) - n).toNat : ℤ) = n + 1 := by omega
      simpa only [heq] using h ((N : ℤ) - n).toNat (by omega)

/-- Let C be abelian, B an object and F:ℤ → Subobject(B) decreasing.
For N∈ℕ assume F⁰=B and F^{N+1}=0, and fix n∈ℤ.
Assume GrᵖF=Coker(Fᵖ⁺¹↪Fᵖ) is zero for every integer p≠n.

The canonical isomorphism GrⁿF ≅ B, formed from the quotient of the zero subobject in Fⁿ and the
  full-subobject inclusion into B. -/
def finiteFiltrationSingleGradeIso
    (F : ℤ → Subobject B) (hF : Antitone F) (N : ℕ)
    (h₀ : F 0 = ⊤) (hN : F ((N : ℤ) + 1) = ⊥)
    (n : ℤ)
    (hz : ∀ p : ℤ, p ≠ n →
      IsZero (cokernel (Subobject.ofLE (F (p + 1)) (F p) (hF (by omega))))) :
    cokernel (Subobject.ofLE (F (n + 1)) (F n) (hF (by omega))) ≅ B := by
  obtain ⟨htop, hbot⟩ := finiteFiltration_singleGrade_endpoints F hF N h₀ hN n hz
  have hi : Subobject.ofLE (F (n + 1)) (F n) (hF (by omega)) = 0 := by
    apply (cancel_mono (F n).arrow).1
    rw [Subobject.ofLE_arrow, hbot, Subobject.bot_arrow, zero_comp]
  letI : IsIso (cokernel.π (Subobject.ofLE (F (n + 1)) (F n) (hF (by omega)))) :=
    cokernel.π_of_zero hi
  letI : IsIso (F n).arrow := (Subobject.isIso_arrow_iff_eq_top _).mpr htop
  exact (asIso (cokernel.π (Subobject.ofLE (F (n + 1)) (F n) (hF (by omega))))).symm ≪≫
    asIso (F n).arrow

/-- Let C be abelian, B an object and F:ℤ → Subobject(B) decreasing.
For N∈ℕ assume F⁰=B and F^{N+1}=0, and fix n∈ℤ.
Assume GrᵖF=Coker(Fᵖ⁺¹↪Fᵖ) is zero for every integer p≠n.

If q:Fⁿ → GrⁿF is the quotient map and ε:GrⁿF ≅ B the canonical comparison, then ε∘q is the
  subobject inclusion Fⁿ↪B. -/
@[reassoc (attr := simp)]
theorem finiteFiltrationSingleGradeIso_π
    (F : ℤ → Subobject B) (hF : Antitone F) (N : ℕ)
    (h₀ : F 0 = ⊤) (hN : F ((N : ℤ) + 1) = ⊥)
    (n : ℤ)
    (hz : ∀ p : ℤ, p ≠ n →
      IsZero (cokernel (Subobject.ofLE (F (p + 1)) (F p) (hF (by omega))))) :
    cokernel.π (Subobject.ofLE (F (n + 1)) (F n) (hF (by omega))) ≫
        (finiteFiltrationSingleGradeIso F hF N h₀ hN n hz).hom = (F n).arrow := by
  dsimp only [finiteFiltrationSingleGradeIso, Iso.trans_hom, Iso.symm_hom, asIso_hom, asIso_inv]
  simp only [IsIso.hom_inv_id_assoc]

/-- Let C be abelian and F,G decreasing filtrations of B,B′, with common
N∈ℕ, F⁰=B,G⁰=B′, F^{N+1}=G^{N+1}=0, and all graded pieces
outside n∈ℤ zero. Suppose f:B → B′ and
a₀:Fⁿ⁺¹ → Gⁿ⁺¹, a₁:Fⁿ → Gⁿ form a commuting square of the
filtration inclusions, with a₁ compatible with f on the ambient
subobject inclusions. The induced quotient map Q satisfies
ε_G∘Q=f∘ε_F for the canonical comparisons GrⁿF ≅ B and GrⁿG ≅ B′. -/
@[reassoc]
theorem finiteFiltrationSingleGradeIso_naturality
    {B' : C} (F : ℤ → Subobject B) (G : ℤ → Subobject B')
    (hF : Antitone F) (hG : Antitone G) (N : ℕ)
    (hF₀ : F 0 = ⊤) (hFN : F ((N : ℤ) + 1) = ⊥)
    (hG₀ : G 0 = ⊤) (hGN : G ((N : ℤ) + 1) = ⊥)
    (n : ℤ)
    (hzF : ∀ p : ℤ, p ≠ n →
      IsZero (cokernel (Subobject.ofLE (F (p + 1)) (F p) (hF (by omega)))))
    (hzG : ∀ p : ℤ, p ≠ n →
      IsZero (cokernel (Subobject.ofLE (G (p + 1)) (G p) (hG (by omega)))))
    (f : B ⟶ B') (a₀ : (F (n + 1) : C) ⟶ (G (n + 1) : C))
    (a₁ : (F n : C) ⟶ (G n : C))
    (hw : Subobject.ofLE (F (n + 1)) (F n) (hF (by omega)) ≫ a₁ =
      a₀ ≫ Subobject.ofLE (G (n + 1)) (G n) (hG (by omega)))
    (ha : a₁ ≫ (G n).arrow = (F n).arrow ≫ f) :
    cokernel.map (Subobject.ofLE (F (n + 1)) (F n) (hF (by omega)))
        (Subobject.ofLE (G (n + 1)) (G n) (hG (by omega))) a₀ a₁ hw ≫
          (finiteFiltrationSingleGradeIso G hG N hG₀ hGN n hzG).hom =
      (finiteFiltrationSingleGradeIso F hF N hF₀ hFN n hzF).hom ≫ f := by
  apply (cancel_epi (cokernel.π (Subobject.ofLE (F (n + 1)) (F n) (hF (by omega))))).1
  dsimp only [cokernel.map]
  rw [cokernel.π_desc_assoc, Category.assoc, finiteFiltrationSingleGradeIso_π,
    finiteFiltrationSingleGradeIso_π_assoc, ha]

end CategoryTheory.Subobject
