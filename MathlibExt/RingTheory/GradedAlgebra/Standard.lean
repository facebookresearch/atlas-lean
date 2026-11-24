/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua, Avocado
module

public import Mathlib.RingTheory.GradedAlgebra.FiniteType
public import Mathlib.RingTheory.HopkinsLevitzki

/-!
# Standard graded algebra presentations

A standard graded presentation is a finite family of degree-one elements
that generates the total algebra over its coefficient ring.  Such a
presentation gives finite type; over an Artinian coefficient ring it also
gives a Noetherian total ring.  It also induces the ordinary polynomial
algebra map sending each variable to the corresponding generator, and that
map is surjective.

This file contains only presentation data and these two structural
consequences together with the ordinary polynomial-algebra map.  It proves
no injectivity, polynomial equivalence, graded algebra-map packaging, free
module presentation, Hilbert--Serre theorem, graded quotient theorem,
Hilbert--Samuel polynomiality, or dimension result.

## Main declarations

* `HilbertSamuel.StandardGradedPresentation`
* `HilbertSamuel.StandardGradedPresentation.finiteType`
* `HilbertSamuel.StandardGradedPresentation.isNoetherianRing_of_isArtinianRing`
* `HilbertSamuel.StandardGradedPresentation.polynomialAlgHom`
* `HilbertSamuel.StandardGradedPresentation.polynomialAlgHom_X`
* `HilbertSamuel.StandardGradedPresentation.polynomialAlgHom_surjective`
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace HilbertSamuel

universe u v

/-- A finite degree-one generating family for a Nat-graded algebra.  The
family need not be minimal. -/
structure StandardGradedPresentation
    (A : Type u) [CommRing A]
    (S : Type v) [CommRing S] [Algebra A S]
    (Sgrade : ℕ → Submodule A S) [GradedAlgebra Sgrade]
    (r : ℕ) where
  /-- The actual degree-one generating family. -/
  generator : Fin r → Sgrade 1
  adjoin_eq_top :
    Algebra.adjoin A (Set.range fun i => (generator i : S)) = ⊤

namespace StandardGradedPresentation

variable {A : Type u} [CommRing A]
variable {S : Type v} [CommRing S] [Algebra A S]
variable {Sgrade : ℕ → Submodule A S} [GradedAlgebra Sgrade]
variable {r : ℕ}

/-- A standard graded presentation makes the total algebra finite type over
its coefficient ring. -/
theorem finiteType
    (hstd : StandardGradedPresentation A S Sgrade r) :
    Algebra.FiniteType A S := by
  classical
  let s : Finset S :=
    Finset.univ.image fun i => (hstd.generator i : S)
  refine ⟨s, ?_⟩
  simpa [s] using hstd.adjoin_eq_top

/-- A standard graded algebra over an Artinian coefficient ring is
Noetherian. -/
theorem isNoetherianRing_of_isArtinianRing
    [IsArtinianRing A]
    (hstd : StandardGradedPresentation A S Sgrade r) :
    IsNoetherianRing S := by
  let _ : Algebra.FiniteType A S := hstd.finiteType
  exact Algebra.FiniteType.isNoetherianRing A S

/-- The ordinary polynomial algebra map associated to a standard graded
presentation sends each variable to the corresponding degree-one generator. -/
noncomputable def polynomialAlgHom
    (hstd : StandardGradedPresentation A S Sgrade r) :
    MvPolynomial (Fin r) A →ₐ[A] S :=
  MvPolynomial.aeval (R := A) fun i => (hstd.generator i : S)

/-- A variable maps to the corresponding standard generator. -/
@[simp]
theorem polynomialAlgHom_X
    (hstd : StandardGradedPresentation A S Sgrade r) (i : Fin r) :
    hstd.polynomialAlgHom (MvPolynomial.X i) = hstd.generator i := by
  simp [polynomialAlgHom]

/-- The polynomial algebra map of a standard graded presentation is
surjective. -/
theorem polynomialAlgHom_surjective
    (hstd : StandardGradedPresentation A S Sgrade r) :
    Function.Surjective hstd.polynomialAlgHom := by
  rw [← AlgHom.range_eq_top, polynomialAlgHom,
    ← Algebra.adjoin_range_eq_range_aeval]
  exact hstd.adjoin_eq_top

end StandardGradedPresentation

end HilbertSamuel
