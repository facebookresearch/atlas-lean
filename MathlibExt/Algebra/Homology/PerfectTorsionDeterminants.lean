/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.RingTheory.Localization.Basic

/-!
# Actual local determinant of a perfect torsion complex

The total quotient ring inverts the actual nonzero divisors, retaining
nilpotents. A bounded finite-free complex is presented by its genuine
homogeneous bases. The scalar-extended complex has an actual contracting
homotopy with h²=0. The local torsion is the determinant of d+h from
the odd part to the even part in those bases. A map in degrees [-1,0]
therefore gives its ordinary positive determinant.

Reference: Fantechi–Pandharipande math/9905104v1, §1.2;
Knudsen–Mumford, determinant of a perfect complex.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.Algebra.Homology.PerfectTorsionDeterminants

open _root_.CategoryTheory
open CochainComplex.HomComplex
open scoped ChangeOfRings

universe u
variable {R : Type u} [CommRing R]

/-- The actual total quotient ring, using every nonzero divisor. -/
abbrev TotalQuotient (R : Type u) [CommRing R] := Localization (nonZeroDivisors R)

/-- Scalar extension of the actual complex to its total quotient ring. -/
def totalComplex (C : CochainComplex (ModuleCat.{u} R) ℤ) :
    CochainComplex (ModuleCat.{u} (TotalQuotient R)) ℤ :=
  ((ModuleCat.extendScalars (algebraMap R (TotalQuotient R))).mapHomologicalComplex (.up ℤ)).obj C

/-- A finite-free torsion presentation retains the actual complex, bases and homotopy. -/
structure TorsionPresentation (C : CochainComplex (ModuleCat.{u} R) ℤ) where
  size : ℕ
  degree : Fin size → ℤ
  basis : ∀ n : ℤ, Module.Basis {i : Fin size // degree i = n} R (C.X n)
  totalBasis : ∀ n : ℤ, Module.Basis {i : Fin size // degree i = n}
    (TotalQuotient R) ((totalComplex C).X n)
  normalized : ∀ (n : ℤ) (i : {i : Fin size // degree i = n}),
    totalBasis n i = (1 : TotalQuotient R) ⊗ₜ[R, algebraMap R (TotalQuotient R)] (basis n i)
  homotopy : Cochain (totalComplex C) (totalComplex C) (-1)
  contraction : δ (-1) 0 homotopy = Cochain.ofHom (𝟙 (totalComplex C))
  square : homotopy.comp homotopy (by omega : (-1 : ℤ) + -1 = -2) = 0

/-- The actual odd homogeneous basis indexes. -/
abbrev OddIndex {C : CochainComplex (ModuleCat.{u} R) ℤ} (P : TorsionPresentation C) :=
  {i : Fin P.size // Odd (P.degree i)}

/-- The actual even homogeneous basis indexes. -/
abbrev EvenIndex {C : CochainComplex (ModuleCat.{u} R) ℤ} (P : TorsionPresentation C) :=
  {i : Fin P.size // Even (P.degree i)}

/-- The actual differential coefficient in the extended finite-free basis. -/
def differentialCoefficient {C : CochainComplex (ModuleCat.{u} R) ℤ}
    (P : TorsionPresentation C) (i j : Fin P.size) : TotalQuotient R :=
  (P.totalBasis (P.degree i)).repr
    (((totalComplex C).d (P.degree j) (P.degree i)).hom
      (P.totalBasis (P.degree j) ⟨j, rfl⟩)) ⟨i, rfl⟩

/-- The actual contracting-homotopy coefficient; every other degree is zero. -/
def homotopyCoefficient {C : CochainComplex (ModuleCat.{u} R) ℤ}
    (P : TorsionPresentation C) (i j : Fin P.size) : TotalQuotient R :=
  if h : P.degree j + (-1 : ℤ) = P.degree i then
    (P.totalBasis (P.degree i)).repr
      ((P.homotopy.v (P.degree j) (P.degree i) h).hom
        (P.totalBasis (P.degree j) ⟨j, rfl⟩)) ⟨i, rfl⟩
  else 0

/-- The local d+h matrix uses an actual bijection of the parity bases. -/
def torsionMatrix {C : CochainComplex (ModuleCat.{u} R) ℤ}
    (P : TorsionPresentation C) (e : OddIndex P ≃ EvenIndex P) :
    Matrix (OddIndex P) (OddIndex P) (TotalQuotient R) :=
  fun i j => differentialCoefficient P (e i).val j.val + homotopyCoefficient P (e i).val j.val

/-- The source local determinant, with the [-1,0] positive-divisor convention. -/
def torsionDeterminant {C : CochainComplex (ModuleCat.{u} R) ℤ}
    (P : TorsionPresentation C) (e : OddIndex P ≃ EvenIndex P) : TotalQuotient R :=
  Matrix.det (torsionMatrix P e)

end MathlibExt.Algebra.Homology.PerfectTorsionDeterminants
