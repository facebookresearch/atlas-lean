/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.AdmissibleMonoFlagStage

/-!
# Canonical selected quotients of admissible monomorphisms

An admissible monomorphism `f : A ⟶ B` gives the zero-based two-step flag
`0 ⟶ A ⟶ B`.  Applying the existing quotient-completion construction to
the interval `[A,B]` selects a quotient object and projection completing `f`
to an admissible exact sequence.

This is the object-level quotient needed by the Segal-subdivision map to the
Quillen Q-construction.  It introduces no second quotient mechanism and
makes no functoriality, span-composition, nerve, or realization claim.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits ZeroObject
open CategoryTheory.ExactCategory

universe v u

namespace CategoryTheory.Waldhausen.SConstruction.AdmissibleMonoFlag

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]

/-- The zero-based flag `0 ⟶ A ⟶ B` associated to an admissible
monomorphism `f : A ⟶ B`. -/
noncomputable def ofAdmissibleMono {A B : C} (f : A ⟶ B)
    (hf : IsAdmissibleMono f) : AdmissibleMonoFlag C 2 where
  chain := ComposableArrows.mk₂ (0 : (0 : C) ⟶ A) f
  first_isZero := isZero_zero C
  step_admissible := by
    intro i hi
    have hi' : i = 0 ∨ i = 1 := by omega
    rcases hi' with rfl | rfl
    · change IsAdmissibleMono (0 : (0 : C) ⟶ A)
      exact isAdmissibleMono_f
        (isAdmissibleExact_zero_id (C := C) (isZero_zero C))
    · change IsAdmissibleMono f
      exact hf

/-- The zero-based flag `0 ⟶ A₀ ⟶ A₁ ⟶ A₂ ⟶ A₃` associated to three
successive admissible monomorphisms. -/
noncomputable def ofAdmissibleMonoTriple
    {A₀ A₁ A₂ A₃ : C}
    (f : A₀ ⟶ A₁) (hf : IsAdmissibleMono f)
    (g : A₁ ⟶ A₂) (hg : IsAdmissibleMono g)
    (h : A₂ ⟶ A₃) (hh : IsAdmissibleMono h) :
    AdmissibleMonoFlag C 4 where
  chain := ComposableArrows.mk₄ (0 : (0 : C) ⟶ A₀) f g h
  first_isZero := isZero_zero C
  step_admissible := by
    intro i hi
    have hi' : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases hi' with rfl | rfl | rfl | rfl
    · change IsAdmissibleMono (0 : (0 : C) ⟶ A₀)
      exact isAdmissibleMono_f
        (isAdmissibleExact_zero_id (C := C) (isZero_zero C))
    · change IsAdmissibleMono f
      exact hf
    · change IsAdmissibleMono g
      exact hg
    · change IsAdmissibleMono h
      exact hh

/-- Selected quotient object of an admissible monomorphism. -/
noncomputable abbrev admissibleMonoQuotient {A B : C} (f : A ⟶ B)
    (hf : IsAdmissibleMono f) : C :=
  (ofAdmissibleMono f hf).intervalQuotient
    (1 : Fin 3) (2 : Fin 3) (by decide)

/-- Selected quotient projection of an admissible monomorphism. -/
noncomputable abbrev admissibleMonoQuotientπ {A B : C} (f : A ⟶ B)
    (hf : IsAdmissibleMono f) :
    B ⟶ admissibleMonoQuotient f hf :=
  (ofAdmissibleMono f hf).intervalπ
    (1 : Fin 3) (2 : Fin 3) (by decide)

/-- The admissible mono followed by its selected quotient projection is
zero. -/
@[reassoc (attr := simp)]
theorem comp_admissibleMonoQuotientπ {A B : C} (f : A ⟶ B)
    (hf : IsAdmissibleMono f) :
    f ≫ admissibleMonoQuotientπ f hf = 0 := by
  exact (ofAdmissibleMono f hf).interval_comp_π
    (1 : Fin 3) (2 : Fin 3) (by decide)

/-- The selected quotient completes the original admissible monomorphism to
an admissible exact sequence. -/
theorem admissibleMonoQuotient_exact {A B : C} (f : A ⟶ B)
    (hf : IsAdmissibleMono f) :
    IsAdmissibleExact
      (ShortComplex.mk f (admissibleMonoQuotientπ f hf)
        (comp_admissibleMonoQuotientπ f hf)) := by
  exact (ofAdmissibleMono f hf).interval_exact
    (1 : Fin 3) (2 : Fin 3) (by decide)

/-- Equal admissible monomorphisms have canonically isomorphic selected
quotients, independently of the proofs of admissibility. -/
noncomputable def admissibleMonoQuotientIsoOfEq
    {A B : C} {f g : A ⟶ B}
    (hf : IsAdmissibleMono f) (hg : IsAdmissibleMono g)
    (h : f = g) :
    admissibleMonoQuotient f hf ≅ admissibleMonoQuotient g hg := by
  subst g
  exact (isColimit_cokernelCofork_of_isAdmissibleExact
    (admissibleMonoQuotient_exact f hf)).coconePointUniqueUpToIso
      (isColimit_cokernelCofork_of_isAdmissibleExact
        (admissibleMonoQuotient_exact f hg))

/-- The quotient comparison for equal admissible monomorphisms carries the
first selected quotient projection to the second. -/
@[reassoc (attr := simp)]
theorem admissibleMonoQuotientπ_isoOfEq_hom
    {A B : C} {f g : A ⟶ B}
    (hf : IsAdmissibleMono f) (hg : IsAdmissibleMono g)
    (h : f = g) :
    admissibleMonoQuotientπ f hf ≫
        (admissibleMonoQuotientIsoOfEq hf hg h).hom =
      admissibleMonoQuotientπ g hg := by
  subst g
  exact IsColimit.comp_coconePointUniqueUpToIso_hom
    (isColimit_cokernelCofork_of_isAdmissibleExact
      (admissibleMonoQuotient_exact f hf))
    (isColimit_cokernelCofork_of_isAdmissibleExact
      (admissibleMonoQuotient_exact f hg))
    WalkingParallelPair.one

end CategoryTheory.Waldhausen.SConstruction.AdmissibleMonoFlag

end
