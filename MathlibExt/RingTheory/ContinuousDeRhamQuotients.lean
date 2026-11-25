/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.RingTheory.DeRhamSource.Complex
public import Mathlib.Topology.Algebra.Module.Basic
public import Mathlib.Topology.Algebra.IsUniformGroup.Defs

/-!
# Continuous affinoid differentials and their native de Rham descent

An analytic differential module is a continuous universal quotient of
raw Kaehler differentials. The quotient, continuous topology and
universal property are source integration inputs; its differential is
the uniquely proved quotient differential from the completed public
Stacks port. Connections and every degree extension are that same
completed source construction. No raw Kaehler identification of arbitrary
global sections is made.

Sources: AxiomMath/Stacks `c496df0d9beea9deaeabcea8492605f9a0a2313b`,
Apache 2.0, Stacks Tags 07HY and 07I0, exact completed Atlas PR2245
`76de3f2665f9c44b06932f9861ee9aae65e04395`; Scholze,
arXiv:1205.3463v2, Definition 6.8 and Proposition 8.5.
-/

set_option backward.isDefEq.respectTransparency false

@[expose] public noncomputable section

namespace MathlibExt.RingTheory.ContinuousDeRhamQuotients

open _root_.CategoryTheory _root_.KaehlerDifferential
open MathlibExt.DeRhamSource
open MathlibExt.DeRhamSource.Stacks.DeRham.DifferentialDescent
open scoped TensorProduct

universe u

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
  [TopologicalSpace A] [TopologicalSpace B] [IsTopologicalRing A] [IsTopologicalRing B]

/-- The continuous universal quotient on an actual affinoid ring map. -/
structure ContinuousQuotient where
  omega : ModuleCat.{u} B
  [uniformSpace : UniformSpace omega]
  [uniformAdd : IsUniformAddGroup omega]
  [continuousSMul : ContinuousSMul B omega]
  [complete : CompleteSpace omega]
  [hausdorff : T2Space omega]
  quotient : Ω[B⁄A] →ₗ[B] omega
  surjective : Function.Surjective quotient
  generation : (sourceDeRham A B).GenerationHypothesis quotient
  continuous : Continuous (fun b : B => quotient (D A B b))
  universal : ∀ (M : Type u) [AddCommGroup M] [Module B M] [Module A M]
    [IsScalarTower A B M] [UniformSpace M]
    [IsUniformAddGroup M] [ContinuousSMul B M] [CompleteSpace M] [T2Space M]
    (d : Derivation A B M), Continuous d →
      ∃! l : omega →ₗ[B] M, Continuous l ∧ ∀ b, l (quotient (D A B b)) = d b

attribute [instance] ContinuousQuotient.uniformSpace ContinuousQuotient.uniformAdd
  ContinuousQuotient.continuousSMul ContinuousQuotient.complete ContinuousQuotient.hausdorff

namespace ContinuousQuotient

variable {A B} (Q : ContinuousQuotient A B)

/-- The proved unique quotient differential; no new family of differentials is assumed. -/
def differential : ∀ n : ℕ, TgtA A B Q.omega n →ₗ[A] TgtA A B Q.omega (n + 1) :=
  Classical.choose (exists_unique_quotient_deRhamDifferential (sourceDeRham A B)
    Q.quotient Q.surjective Q.generation)

theorem differential_commutes : (sourceDeRham A B).Commutes Q.quotient Q.differential :=
  (Classical.choose_spec (exists_unique_quotient_deRhamDifferential (sourceDeRham A B)
    Q.quotient Q.surjective Q.generation)).1

theorem differential_square (n : ℕ) :
    (Q.differential (n + 1)).comp (Q.differential n) = 0 :=
  (Classical.choose_spec (exists_unique_quotient_deRhamDifferential (sourceDeRham A B)
    Q.quotient Q.surjective Q.generation)).2.2.2 n

/-- The continuous quotient de Rham complex is constructed by the native cochain constructor. -/
def complex : CochainComplex (ModuleCat.{u} A) ℕ :=
  CochainComplex.of (fun n => ModuleCat.of A (TgtA A B Q.omega n))
    (fun n => ModuleCat.ofHom (Q.differential n))
    (fun n => ModuleCat.hom_ext (Q.differential_square n))

variable (M : Type u) [AddCommGroup M] [Module B M]

abbrev NativeConnection := Crystalline.Connection A B Q.quotient M

/-- The actual completed public source extends the connection in every degree. -/
def extended (nabla : Q.NativeConnection M) :=
  Crystalline.extendedConnection (sourceDeRham A B) Q.quotient Q.surjective Q.generation nabla

def IsIntegrable (nabla : Q.NativeConnection M) : Prop :=
  Crystalline.Connection.IsIntegrable (sourceDeRham A B) Q.quotient Q.surjective Q.generation nabla

/-- The unresolved square-zero implication has this direct, source-qualified proof target. -/
def ExtensionSquareZero (nabla : Q.NativeConnection M) : Prop :=
  ∀ n : ℕ, ((Q.extended M nabla).toLinearMap (n + 1)).comp
    ((Q.extended M nabla).toLinearMap n) = 0

/-- Given that proof, the coefficient complex uses exactly the native extended connection. -/
def connectionComplex (nabla : Q.NativeConnection M) (h : Q.ExtensionSquareZero M nabla) :
    CochainComplex (ModuleCat.{u} A) ℕ :=
  CochainComplex.of
    (fun n => ModuleCat.of A (RestrictScalars A B (M ⊗[B] (⋀[B]^n Q.omega))))
    (fun n => ModuleCat.ofHom ((Q.extended M nabla).toLinearMap n))
    (fun n => ModuleCat.hom_ext (h n))

end ContinuousQuotient

end MathlibExt.RingTheory.ContinuousDeRhamQuotients
