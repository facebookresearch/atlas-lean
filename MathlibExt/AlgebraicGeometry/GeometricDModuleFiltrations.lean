/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.HolomorphicCoefficientSheaves
public import MathlibExt.AlgebraicGeometry.DifferentialOperatorScalars
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import MathlibExt.AlgebraicGeometry.LocalFinitePresentation
public import Mathlib.CategoryTheory.Subobject.Lattice
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels

/-!
# Actual filtered sheaves of differential modules

Filtration terms are O-subobjects of the actual scalar-restricted D-module.
Order acts through the actual finite-order presheaf and its sheafification
unit. Exhaustivity and the lower bound are local, as required on noncompact
manifolds. Goodness requires finitely many shifted local generators for the
displayed D action, not merely a list of coherent filtration pieces: near
every point, every section of `F_p` is locally a combination
`∑ⱼ Pⱼ · sⱼ` with `ord Pⱼ + deg sⱼ ≤ p`, that is, the map from the shifted
free module onto `F_p` is an epimorphism of sheaves.

Local finite presentation (`LocalFinitePresentation.LocallyFinitelyPresented`)
is the universal cokernel of two actual finite free sheaves. These definitions
do not declare a named holonomic predicate or assume a Riemann--Hilbert
conclusion. Characteristic-symbol support is additional data built from these
actual filtration quotients.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.GeometricDModuleFiltrations

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open DifferentialOperatorSheaves DifferentialOperatorScalars
open MathlibExt.RingTheory.GeometricDifferentialOperators
open MathlibExt.AlgebraicGeometry.LocalFinitePresentation (LocallyFinitelyPresented)
open scoped Manifold ContDiff BigOperators

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]
  (M : Type) [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M]
  [HasSheafify (Opens.grothendieckTopology M) RingCat.{0}]

abbrev coefficients := HolomorphicCoefficientSheaves.coefficientPresheaf E M
abbrev coefficientRing := coefficientSheaf ℂ M (coefficients E M)
abbrev DifferentialModule := DModule ℂ M (coefficients E M)

def underlying (D : DifferentialModule E M) :
    SheafOfModules.{0} (coefficientRing E M) :=
  (underlyingO ℂ M (coefficients E M)).obj D

abbrev Section (D : DifferentialModule E M) (U : Opens M) := D.val.obj (op U)

def restrictSection (D : DifferentialModule E M) {U V : Opens M} (h : V ≤ U) :
    Section E M D U → Section E M D V :=
  (D.val.map (homOfLE h).op).hom

def OrderOn {U : Opens M}
    (P : finiteOperatorRing ℂ M (coefficients E M) U) (n : ℕ) : Prop :=
  ∀ V : Inside M U, OrderLE ℂ ((coefficients E M).obj (op V.val)) n (P.val.val V)

def operatorValue {U : Opens M}
    (P : finiteOperatorRing ℂ M (coefficients E M) U) :
    (differentialRing ℂ M (coefficients E M)).obj.obj (op U) :=
  ((toSheafify (Opens.grothendieckTopology M)
    (operatorPresheaf ℂ M (coefficients E M))).app (op U)).hom P

def act {U : Opens M} (D : DifferentialModule E M)
    (P : finiteOperatorRing ℂ M (coefficients E M) U) (s : Section E M D U) :
    Section E M D U := operatorValue E M P • s

def InFiltration (D : DifferentialModule E M) (F : ℤ → Subobject (underlying E M D))
    (p : ℤ) (U : Opens M) (s : Section E M D U) : Prop :=
  ∃ t : (Subobject.underlying.obj (F p)).val.obj (op U),
    ((F p).arrow.val.app (op U)).hom t = s

variable [HasSheafify (Opens.grothendieckTopology M) AddCommGrpCat.{0}]
  [(Opens.grothendieckTopology M).WEqualsLocallyBijective AddCommGrpCat.{0}]
  [∀ U : Opens M, HasWeakSheafify
    ((Opens.grothendieckTopology M).over U) AddCommGrpCat.{0}]
  [∀ U : Opens M, ((Opens.grothendieckTopology M).over U).WEqualsLocallyBijective
    AddCommGrpCat.{0}]

/-- A good filtration of a left differential module by coherent `O`-submodules. -/
structure GoodFiltration where
  object : DifferentialModule E M
  term : ℤ → Subobject (underlying E M object)
  monotone : Monotone term
  boundedBelow : ∀ x : M, ∃ U : Opens M, x ∈ U ∧ ∃ p : ℤ,
    ∀ q < p, ∀ (V : Opens M), V ≤ U → ∀ s : Section E M object V,
      InFiltration E M object term q V s → s = 0
  locallyPresented : ∀ p, LocallyFinitelyPresented M (coefficientRing E M)
    (Subobject.underlying.obj (term p))
  exhaustive : ∀ (U : Opens M) (s : Section E M object U) (x : U),
    ∃ (V : Opens M) (hV : V ≤ U), x.val ∈ V ∧
      ∃ p : ℤ, InFiltration E M object term p V (restrictSection E M object hV s)
  orderAction : ∀ (U : Opens M) (p : ℤ) (n : ℕ)
    (P : finiteOperatorRing ℂ M (coefficients E M) U), OrderOn E M P n →
    ∀ s : Section E M object U, InFiltration E M object term p U s →
      InFiltration E M object term (p + n) U (act E M object P s)
  localGenerators : ∀ x : M, ∃ U : Opens M, x ∈ U ∧
    ∃ (r : ℕ) (degree : Fin r → ℤ) (generators : Fin r → Section E M object U),
      (∀ j, InFiltration E M object term (degree j) U (generators j)) ∧
      ∀ (V : Opens M) (hV : V ≤ U) (p : ℤ) (s : Section E M object V),
        InFiltration E M object term p V s → ∀ y ∈ V,
        ∃ (W : Opens M) (hW : W ≤ V), y ∈ W ∧
        ∃ (n : Fin r → ℕ) (P : Fin r → finiteOperatorRing ℂ M (coefficients E M) W),
          (∀ j, P j = 0 ∨ (OrderOn E M (P j) (n j) ∧ (n j : ℤ) + degree j ≤ p)) ∧
            restrictSection E M object hW s =
              ∑ j, act E M object (P j)
                (restrictSection E M object (hW.trans hV) (generators j))

def filtrationStep (F : GoodFiltration E M) (p : ℤ) :
    Subobject.underlying.obj (F.term (p - 1)) ⟶ Subobject.underlying.obj (F.term p) :=
  Subobject.underlying.map (homOfLE (F.monotone (by omega)))

/-- The graded term is the actual cokernel of the consecutive O-subobject inclusion. -/
def gradedPiece (F : GoodFiltration E M) (p : ℤ) :
    SheafOfModules.{0} (coefficientRing E M) := cokernel (filtrationStep E M F p)

end MathlibExt.AlgebraicGeometry.GeometricDModuleFiltrations

