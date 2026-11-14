/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Adapted from AxiomMath/Stacks, revision
c496df0d9beea9deaeabcea8492605f9a0a2313b,
StacksFrontier/AlgebraicGeometry/Chow/Vocabulary.lean,
StacksFrontier/AlgebraicGeometry/Chow/CycleAssociatedClosed/Basic.lean,
StacksFrontier/AlgebraicGeometry/Chow/RationalEquivalence/
GeometricRationalEquivalence.lean, under Apache 2.0.
Modifications: use rational coefficients, restrict to finite-type complex
schemes, and present relations by flat affine-line families at 0 and 1.
-/
module

public import Mathlib.AlgebraicGeometry.AlgebraicCycle.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.RingTheory.Length
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Basic.Complex.Basic

/-!
# Concrete cycle and geometric rational-equivalence carriers

The cycles are Mathlib algebraic cycles, indexed by generic scheme points.
Their dimension grading uses `Order.height`, which is the dimension of the
closure of a point for a finite-type complex scheme. Fundamental cycles have
the lengths of the actual generic local rings as multiplicities.

Relations come from integral flat closed families in `X × ℂ[t]`, with their
actual scheme-theoretic fibres at 0 and 1. The quotient is a concrete geometric
presentation. This file does not assert its equivalence with another public
Chow-group model or furnish cohomological cycle classes.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open TopologicalSpace

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.GeometricChow

/-- Complex schemes with a specified structure map. -/
abbrev ComplexScheme := Over (Spec (.of ℂ))

/-- Pointwise rational multiplication on the actual locally finite cycles. -/
def scalarCycle (X : Scheme) (a : ℚ) (c : AlgebraicCycle X ℚ) :
    AlgebraicCycle X ℚ where
  toFun x := a * c x
  supportWithinDomain' := by simp
  supportLocallyFiniteWithinDomain' := by
    intro x _
    obtain ⟨U, hU, hfin⟩ := c.locallyFiniteSupport x
    refine ⟨U, hU, hfin.subset ?_⟩
    intro y hy
    exact ⟨hy.1, right_ne_zero_of_mul hy.2⟩

/-- Rational cycles carry the pointwise rational module structure. -/
instance cycleModule (X : Scheme) : Module ℚ (AlgebraicCycle X ℚ) where
  smul := scalarCycle X
  one_smul c := by ext x; exact one_mul (c x)
  mul_smul a b c := by ext x; exact mul_assoc a b (c x)
  smul_zero a := by ext x; exact mul_zero a
  smul_add a c e := by ext x; exact mul_add a (c x) (e x)
  add_smul a b c := by ext x; exact add_mul a b (c x)
  zero_smul c := by ext x; exact zero_mul (c x)

/-- Rational cycles of a fixed dimension, on actual generic scheme points. -/
def cyclesOfDimension (X : Scheme) (r : ℕ) :
    Submodule ℚ (AlgebraicCycle X ℚ) where
  carrier := {c | ∀ x, c x ≠ 0 → Order.height x = r}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb x hx
    by_cases h : a x = 0
    · exact hb x (by simpa [h] using hx)
    · exact ha x h
  smul_mem' := by
    intro a c hc x hx
    change a * c x ≠ 0 at hx
    exact hc x (right_ne_zero_of_mul hx)

/-- The actual group of rational `r`-cycles. -/
abbrev CycleGroup (X : Scheme) (r : ℕ) := cyclesOfDimension X r

/-- A cycle with every component outside dimension `r` removed. -/
def dimensionPart (X : Scheme) (r : ℕ) (c : AlgebraicCycle X ℚ) :
    CycleGroup X r := by
  classical
  let z : AlgebraicCycle X ℚ :=
    { toFun := fun x => if Order.height x = r then c x else 0
      supportWithinDomain' := by simp
      supportLocallyFiniteWithinDomain' := by
        intro x _
        obtain ⟨U, hU, hfin⟩ := c.locallyFiniteSupport x
        refine ⟨U, hU, hfin.subset ?_⟩
        intro y hy
        refine ⟨hy.1, ?_⟩
        by_cases h : Order.height y = r
        · simpa [Function.mem_support, h] using hy.2
        · simpa [Function.mem_support, h] using hy.2 }
  exact ⟨z, by intro x hx; by_contra h; exact hx (by simp [z, h])⟩

/-- The generic point of an actual irreducible component. -/
def componentPoint (X : Scheme) (Z : irreducibleComponents X) : X :=
  Z.2.1.genericPoint

/-- The length multiplicity of an irreducible component in the scheme. -/
def componentMultiplicity (X : Scheme) (Z : irreducibleComponents X) : ℕ :=
  (Module.length (X.presheaf.stalk (componentPoint X Z))
    (X.presheaf.stalk (componentPoint X Z))).toNat

/-- The fundamental cycle of the actual scheme, with local-ring lengths. -/
def fundamentalCycle (X : Scheme) [IsNoetherian X] :
    AlgebraicCycle X ℚ := by
  classical
  letI : Finite (irreducibleComponents X) :=
    NoetherianSpace.finite_irreducibleComponents.to_subtype
  letI := Fintype.ofFinite (irreducibleComponents X)
  exact ∑ Z : irreducibleComponents X,
    Function.locallyFinsuppWithin.single (componentPoint X Z)
      (componentMultiplicity X Z : ℚ)

/-- Its dimension-`r` component. -/
def fundamentalCycleOfDimension (X : Scheme) [IsNoetherian X] (r : ℕ) :
    CycleGroup X r := dimensionPart X r (fundamentalCycle X)

/-- The affine complex line with its actual structural morphism. -/
def affineLine : ComplexScheme :=
  Over.mk (Spec.map (CommRingCat.ofHom
    (algebraMap ℂ (Polynomial ℂ))))

/-- The complex point of the affine line at `a`. -/
def affinePoint (a : ℂ) : Spec (.of ℂ) ⟶ affineLine.left :=
  Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom a))

/-- The graph of the constant parameter `a` in `X × ℂ[t]`. -/
def parameterSection (X : ComplexScheme) (a : ℂ) :
    X.left ⟶ pullback X.hom affineLine.hom :=
  pullback.lift (𝟙 _) (X.hom ≫ affinePoint a) (by
    have h : CommRingCat.ofHom (algebraMap ℂ (Polynomial ℂ)) ≫
        CommRingCat.ofHom (Polynomial.evalRingHom a) =
          𝟙 (CommRingCat.of ℂ) := by
      ext z
      simp
    simp [affineLine, affinePoint, ← Spec.map_comp, h])

/-- A genuine integral flat closed family in `X × ℂ[t]`. -/
structure FlatFamily (X : ComplexScheme) (r : ℕ) where
  /-- The total scheme. -/
  Y : Scheme
  /-- Its closed embedding into the actual product over `Spec ℂ`. -/
  inclusion : Y ⟶ pullback X.hom affineLine.hom
  /-- Closedness fixes the fibres as closed subschemes of `X`. -/
  [isClosedImmersion : IsClosedImmersion inclusion]
  /-- The total scheme is integral. -/
  [isIntegral : IsIntegral Y]
  /-- The total scheme is Noetherian. -/
  [isNoetherian : IsNoetherian Y]
  /-- The family is flat over the affine parameter line. -/
  [isFlat : Flat (inclusion ≫ pullback.snd X.hom affineLine.hom)]
  /-- The total integral component has dimension `r + 1`. -/
  dimension : Order.height (genericPoint Y) = r + 1
  /-- Noetherianity of the actual scheme-theoretic fibres. -/
  [fibresNoetherian : ∀ a : ℂ,
    IsNoetherian (pullback inclusion (parameterSection X a))]

attribute [instance] FlatFamily.isClosedImmersion FlatFamily.isIntegral
  FlatFamily.isNoetherian FlatFamily.isFlat FlatFamily.fibresNoetherian

namespace FlatFamily

variable {X : ComplexScheme} {r : ℕ} (F : FlatFamily X r)

/-- Scheme-theoretic fibre as a pullback of the actual closed embedding. -/
abbrev fibre (a : ℂ) := pullback F.inclusion (parameterSection X a)

/-- Its closed immersion into `X`. -/
def fibreInclusion (a : ℂ) : F.fibre a ⟶ X.left :=
  pullback.snd F.inclusion (parameterSection X a)

/-- Push the length-weighted fibre cycle to the actual ambient scheme. -/
def fibreCycle (a : ℂ) : CycleGroup X.left r :=
  dimensionPart X.left r
    (AlgebraicCycle.map (F.fibreInclusion a) Order.height Order.height
      (fundamentalCycle (F.fibre a)))

/-- The geometric rational-equivalence generator at parameters 0 and 1. -/
def difference : CycleGroup X.left r := F.fibreCycle 0 - F.fibreCycle 1

end FlatFamily

/-- The rational-equivalence submodule generated by the actual flat families. -/
def rationalEquivalences (X : ComplexScheme) (r : ℕ) :
    Submodule ℚ (CycleGroup X.left r) :=
  Submodule.span ℚ (Set.range (FlatFamily.difference (X := X) (r := r)))

/-- The geometric presentation of rational Chow homology. -/
abbrev ChowGroup (X : ComplexScheme) (r : ℕ) :=
  CycleGroup X.left r ⧸ rationalEquivalences X r

/-- The quotient sends every defining family relation to zero. -/
theorem family_difference_zero (X : ComplexScheme) (r : ℕ)
    (F : FlatFamily X r) :
    (rationalEquivalences X r).mkQ F.difference = 0 := by
  exact (Submodule.Quotient.mk_eq_zero _).2
    (Submodule.subset_span ⟨F, rfl⟩)

end MathlibExt.AlgebraicGeometry.GeometricChow
