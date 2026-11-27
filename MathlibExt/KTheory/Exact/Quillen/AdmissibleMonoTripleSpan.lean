/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.KTheory.Exact.Quillen.AdmissibleMonoFlagSpan
public import MathlibExt.KTheory.Exact.Quillen.AdmissibleMonoQuotient

/-!
# Quillen spans from triples of admissible monomorphisms

A chain `A₀ ↪ A₁ ↪ A₂ ↪ A₃` determines the quotient span

```text
A₂/A₁  ←↞  A₂/A₀  ↪  A₃/A₀.
```

This file builds that span from the existing quotient-completed flag and
compares its source endpoint with the separately selected quotient of the
middle arrow.  It also records admissibility of the total composite, which is
the input for the remaining target-endpoint comparison.

These are the morphism-level ingredients for the Segal-subdivision map.  No
target transport, identity, composition, quotient descent, functor, nerve, or
realization claim is made here.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits
open CategoryTheory.ExactCategory
open AlgebraicKTheory

universe v u

namespace CategoryTheory.Waldhausen.SConstruction.AdmissibleMonoFlag

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]

/-- The zero-based length-four flag associated to three admissible
monomorphisms. -/
noncomputable abbrev admissibleMonoTripleFlag
    {A₀ A₁ A₂ A₃ : C}
    (f : A₀ ⟶ A₁) (hf : IsAdmissibleMono f)
    (g : A₁ ⟶ A₂) (hg : IsAdmissibleMono g)
    (h : A₂ ⟶ A₃) (hh : IsAdmissibleMono h) :
    AdmissibleMonoFlag C 4 :=
  ofAdmissibleMonoTriple f hf g hg h hh

/-- Raw interval span `[A₁,A₂] ←↞ [A₀,A₂] ↪ [A₀,A₃]`. -/
noncomputable def admissibleMonoTripleIntervalSpan
    {A₀ A₁ A₂ A₃ : C}
    (f : A₀ ⟶ A₁) (hf : IsAdmissibleMono f)
    (g : A₁ ⟶ A₂) (hg : IsAdmissibleMono g)
    (h : A₂ ⟶ A₃) (hh : IsAdmissibleMono h) :
    let F := admissibleMonoTripleFlag f hf g hg h hh
    QuillenSpan
      (F.intervalQuotient (2 : Fin 5) (3 : Fin 5) (by decide))
      (F.intervalQuotient (1 : Fin 5) (4 : Fin 5) (by decide)) := by
  let F := admissibleMonoTripleFlag f hf g hg h hh
  exact F.intervalQuillenSpan (by decide) (by decide) (by decide)

/-- The total composite of three admissible monomorphisms is admissible. -/
theorem admissibleMonoTriple_comp_admissible
    {A₀ A₁ A₂ A₃ : C}
    (f : A₀ ⟶ A₁) (hf : IsAdmissibleMono f)
    (g : A₁ ⟶ A₂) (hg : IsAdmissibleMono g)
    (h : A₂ ⟶ A₃) (hh : IsAdmissibleMono h) :
    IsAdmissibleMono ((f ≫ g) ≫ h) :=
  admissibleMono_comp.comp_mem _ _
    (admissibleMono_comp.comp_mem _ _ hf hg) hh

/-- The source interval of the triple flag is the selected quotient of its
middle arrow. -/
noncomputable def admissibleMonoTripleSourceIso
    {A₀ A₁ A₂ A₃ : C}
    (f : A₀ ⟶ A₁) (hf : IsAdmissibleMono f)
    (g : A₁ ⟶ A₂) (hg : IsAdmissibleMono g)
    (h : A₂ ⟶ A₃) (hh : IsAdmissibleMono h) :
    let F := admissibleMonoTripleFlag f hf g hg h hh
    F.intervalQuotient (2 : Fin 5) (3 : Fin 5) (by decide) ≅
      admissibleMonoQuotient g hg := by
  let F := admissibleMonoTripleFlag f hf g hg h hh
  exact F.intervalIsoOfExact (by decide)
    (admissibleMonoQuotientπ g hg)
    (comp_admissibleMonoQuotientπ g hg)
    (admissibleMonoQuotient_exact g hg)

/-- The source interval projection followed by the source comparison is the
selected quotient projection of the middle arrow. -/
@[reassoc (attr := simp)]
theorem admissibleMonoTripleSourceIso_projection
    {A₀ A₁ A₂ A₃ : C}
    (f : A₀ ⟶ A₁) (hf : IsAdmissibleMono f)
    (g : A₁ ⟶ A₂) (hg : IsAdmissibleMono g)
    (h : A₂ ⟶ A₃) (hh : IsAdmissibleMono h) :
    let F := admissibleMonoTripleFlag f hf g hg h hh
    F.intervalπ (2 : Fin 5) (3 : Fin 5) (by decide) ≫
        (admissibleMonoTripleSourceIso f hf g hg h hh).hom =
      admissibleMonoQuotientπ g hg := by
  let F := admissibleMonoTripleFlag f hf g hg h hh
  let h23 : (2 : Fin 5) ≤ (3 : Fin 5) := by decide
  change F.intervalπ (2 : Fin 5) (3 : Fin 5) h23 ≫
      (F.intervalIsoOfExact h23
        (admissibleMonoQuotientπ g hg)
        (comp_admissibleMonoQuotientπ g hg)
        (admissibleMonoQuotient_exact g hg)).hom =
    admissibleMonoQuotientπ g hg
  exact F.intervalπ_intervalIsoOfExact_hom h23
    (admissibleMonoQuotientπ g hg)
    (comp_admissibleMonoQuotientπ g hg)
    (admissibleMonoQuotient_exact g hg)

end CategoryTheory.Waldhausen.SConstruction.AdmissibleMonoFlag

end
