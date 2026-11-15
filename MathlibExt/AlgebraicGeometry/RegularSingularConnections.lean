/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.FieldTheory.RatFunc.Valuation
public import Mathlib.RingTheory.Valuation.Integers
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.Algebra.Polynomial.RingDivision
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import MathlibExt.AlgebraicGeometry.ConstructibleComplexes
public import MathlibExt.Algebra.Homology.TwoTermComplex

/-!
# Regular singular rational connections and actual solution sheaves

The field is `ℂ(t)`. A normalized derivation satisfies `δ(t)=1`, which
uniquely specifies the rational derivative. A matrix specifies the actual
connection `δ-A`. Regular singularity is existence of a full finite lattice
over the actual valuation ring stable under the logarithmic connection;
the infinity condition uses `-t(δ-A)` in the coordinate `1/t`.

Solution sections are actual holomorphic solutions of `s'=A(z)s` on the
punctured complex line. Their presheaf and sheafification are constructed,
rather than supplied as an unrelated functor or named predicate.

Sources: Deligne, *Équations différentielles à points singuliers réguliers*,
Lecture Notes in Mathematics 163 (1970), Chapters I and II, especially II §5.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.RegularSingularConnections

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped Matrix

/-- The actual rational function field of the complex affine line. -/
abbrev RationalFunctions := RatFunc ℂ

/-- A derivation of `ℂ(t)` normalized by the actual rational coordinate.
This is characterized toolbox data, not an existence axiom. -/
structure RationalDerivative where
  derivation : Derivation ℂ RationalFunctions RationalFunctions
  coordinate : derivation (RatFunc.X : RationalFunctions) = 1

/-- The actual connection operator associated with a rational matrix. -/
def connection (δ : RationalDerivative) {r : ℕ}
    (A : Matrix (Fin r) (Fin r) RationalFunctions) (v : Fin r → RationalFunctions) :
    Fin r → RationalFunctions := fun i ↦ δ.derivation (v i) - (A.mulVec v) i

/-- The actual complex-linear connection endomorphism. -/
def connectionLinearMap (δ : RationalDerivative) {r : ℕ}
    (A : Matrix (Fin r) (Fin r) RationalFunctions) :
    Module.End ℂ (Fin r → RationalFunctions) where
  toFun := connection δ A
  map_add' := by
    intro v w
    ext i
    simp [connection, Matrix.mulVec_add]
    ring
  map_smul' := by
    intro c v
    ext i
    simp [connection, Matrix.mulVec_smul, smul_sub]

/-- The rational connection has the actual Leibniz action of differential
operators, not a free linear endomorphism named a connection. -/
theorem connection_leibniz (δ : RationalDerivative) {r : ℕ}
    (A : Matrix (Fin r) (Fin r) RationalFunctions)
    (a : RationalFunctions) (v : Fin r → RationalFunctions) :
    connection δ A (a • v) = a • connection δ A v + δ.derivation a • v := by
  ext i
  simp [connection, Matrix.mulVec_smul, Derivation.leibniz, smul_eq_mul]
  ring

/-- Actual local valuation at the finite point `t=a`. -/
def finitePlace (a : ℂ) : IsDedekindDomain.HeightOneSpectrum (Polynomial ℂ) where
  asIdeal := Ideal.span {Polynomial.X - Polynomial.C a}
  isPrime := by
    rw [Ideal.span_singleton_prime]
    exacts [Polynomial.prime_X_sub_C a, Polynomial.X_sub_C_ne_zero a]
  ne_bot := by
    rw [ne_eq, Ideal.span_singleton_eq_bot]
    exact Polynomial.X_sub_C_ne_zero a

/-- The actual valuation ring of rational functions regular at `a`. -/
def finiteLocalRing (a : ℂ) : Subring RationalFunctions :=
  ((finitePlace a).valuation RationalFunctions).integer

/-- The actual valuation ring of rational functions regular at infinity. -/
def infinityLocalRing : Subring RationalFunctions := by
  classical
  exact (RatFunc.inftyValuation ℂ).integer

/-- A full finite logarithmic lattice at a finite point. -/
def RegularSingularAt (δ : RationalDerivative) {r : ℕ}
    (A : Matrix (Fin r) (Fin r) RationalFunctions) (a : ℂ) : Prop :=
  ∃ Λ : Submodule (finiteLocalRing a) (Fin r → RationalFunctions),
    Λ.FG ∧ Submodule.span RationalFunctions (Λ : Set (Fin r → RationalFunctions)) = ⊤ ∧
      ∀ v, v ∈ Λ → (RatFunc.X - RatFunc.C a) • connection δ A v ∈ Λ

/-- Regular singularity at infinity, with its actual logarithmic operator
`u∇_(∂u)=-t∇_(∂t)`, where `u=1/t`. -/
def RegularSingularAtInfinity (δ : RationalDerivative) {r : ℕ}
    (A : Matrix (Fin r) (Fin r) RationalFunctions) : Prop :=
  ∃ Λ : Submodule infinityLocalRing (Fin r → RationalFunctions),
    Λ.FG ∧ Submodule.span RationalFunctions (Λ : Set (Fin r → RationalFunctions)) = ⊤ ∧
      ∀ v, v ∈ Λ → (-RatFunc.X : RationalFunctions) • connection δ A v ∈ Λ

/-- The punctured complex line, with the actual subspace topology. -/
def puncturedLine (S : Finset ℂ) : TopCat.{0} := TopCat.of {z : ℂ | z ∉ S}

/-- Actual affine points of a punctured-line open. -/
def ambientOpen (S : Finset ℂ) (U : Opens (puncturedLine S)) : Set ℂ :=
  Subtype.val '' (U : Set (puncturedLine S))

/-- Every coefficient denominator is nonzero away from the selected poles. -/
def PolesWithin (S : Finset ℂ) {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) RationalFunctions) : Prop :=
  ∀ z : ℂ, z ∉ S → ∀ i j, (A i j).denom.eval z ≠ 0

/-- Evaluation of a matrix coefficient at an actual non-pole. -/
def evaluated {m n : ℕ} (A : Matrix (Fin m) (Fin n) RationalFunctions)
    (z : ℂ) : Matrix (Fin m) (Fin n) ℂ :=
  fun i j ↦ RatFunc.eval (RingHom.id ℂ) z (A i j)

/-- Actual solution sections. Zero extension outside the open makes their
global function representatives unique; derivatives are checked within
the actual open, so that extension does not impose a boundary condition. -/
def solutionSections {r : ℕ} (S : Finset ℂ)
    (A : Matrix (Fin r) (Fin r) RationalFunctions) (U : Opens (puncturedLine S)) :
    Submodule ℂ (ℂ → EuclideanSpace ℂ (Fin r)) where
  carrier := {s | (∀ z, z ∉ ambientOpen S U → s z = 0) ∧
    ∀ z, z ∈ ambientOpen S U → ∀ i,
      HasDerivWithinAt (fun t ↦ s t i) ((evaluated A z).mulVec (s z) i)
        (ambientOpen S U) z}
  zero_mem' := by
    constructor
    · intro z hz; rfl
    · intro z hz i
      simpa [Matrix.mulVec, dotProduct] using
        (hasDerivWithinAt_const z (ambientOpen S U) (0 : ℂ))
  add_mem' := by
    intro s t hs ht
    constructor
    · intro z hz
      simp [hs.1 z hz, ht.1 z hz]
    · intro z hz i
      convert (hs.2 z hz i).add (ht.2 z hz i) using 1
      · ext u; simp
      · simp [Matrix.mulVec, dotProduct, mul_add, Finset.sum_add_distrib]
  smul_mem' := by
    intro c s hs
    constructor
    · intro z hz
      simp [hs.1 z hz]
    · intro z hz i
      convert (hs.2 z hz i).const_mul c using 1
      · ext u; simp
      · simp [Matrix.mulVec, dotProduct, mul_left_comm, Finset.mul_sum]

/-- Holomorphic vector functions on an actual punctured-line open. -/
def holomorphicSections (S : Finset ℂ) (r : ℕ) (U : Opens (puncturedLine S)) :
    Submodule ℂ (ℂ → EuclideanSpace ℂ (Fin r)) where
  carrier := {s | (∀ z, z ∉ ambientOpen S U → s z = 0) ∧
    ∀ z, z ∈ ambientOpen S U → ∀ i,
      DifferentiableWithinAt ℂ (fun t ↦ s t i) (ambientOpen S U) z}
  zero_mem' := by
    constructor
    · intro z hz; rfl
    · intro z hz i
      exact differentiableWithinAt_const _
  add_mem' := by
    intro s t hs ht
    constructor
    · intro z hz; simp [hs.1 z hz, ht.1 z hz]
    · intro z hz i
      convert (hs.2 z hz i).add (ht.2 z hz i) using 1
      ext u; simp
  smul_mem' := by
    intro c s hs
    constructor
    · intro z hz; simp [hs.1 z hz]
    · intro z hz i
      convert (hs.2 z hz i).const_smul c using 1
      ext u; simp

/-- A geometric two-term de Rham sheaf realization of the actual matrix
connection. The two terms are holomorphic vector functions and their `dt`
coefficients, respectively; every local differential is the actual
derivative minus the evaluated rational matrix. -/
structure AnalyticConnectionDeRhamData (S : Finset ℂ) (r : ℕ)
    (A : Matrix (Fin r) (Fin r) RationalFunctions) where
  functions : TopCat.Sheaf (ModuleCat.{0} ℂ) (puncturedLine S)
  forms : TopCat.Sheaf (ModuleCat.{0} ℂ) (puncturedLine S)
  functionSections (U : Opens (puncturedLine S)) :
    functions.obj.obj (op U) ≃ₗ[ℂ] holomorphicSections S r U
  formSections (U : Opens (puncturedLine S)) :
    forms.obj.obj (op U) ≃ₗ[ℂ] holomorphicSections S r U
  function_restriction (U V : Opens (puncturedLine S)) (h : V ≤ U)
      (s : functions.obj.obj (op U)) (z : ℂ) (hz : z ∈ ambientOpen S V) :
    (functionSections V (functions.obj.map (homOfLE h).op s)).1 z =
      (functionSections U s).1 z
  form_restriction (U V : Opens (puncturedLine S)) (h : V ≤ U)
      (s : forms.obj.obj (op U)) (z : ℂ) (hz : z ∈ ambientOpen S V) :
    (formSections V (forms.obj.map (homOfLE h).op s)).1 z =
      (formSections U s).1 z
  differential : functions ⟶ forms
  differential_normalization (U : Opens (puncturedLine S))
      (s : functions.obj.obj (op U)) (z : ℂ) (hz : z ∈ ambientOpen S U) (i : Fin r) :
    (formSections U (differential.hom.app (op U) s)).1 z i =
      derivWithin (fun t ↦ (functionSections U s).1 t i) (ambientOpen S U) z -
        ((evaluated A z).mulVec ((functionSections U s).1 z)) i

/-- The actual unshifted analytic connection de Rham complex, in degrees
zero and one. Its perverse normalization on a curve is the shift `[1]`. -/
def analyticDeRhamComplex {S : Finset ℂ} {r : ℕ}
    {A : Matrix (Fin r) (Fin r) RationalFunctions}
    (D : AnalyticConnectionDeRhamData S r A) :
    CochainComplex (TopCat.Sheaf (ModuleCat.{0} ℂ) (puncturedLine S)) ℕ :=
  MathlibExt.Algebra.Homology.twoTermComplex D.differential

theorem ambientOpen_mono (S : Finset ℂ) {U V : Opens (puncturedLine S)} (h : V ≤ U) :
    ambientOpen S V ⊆ ambientOpen S U := by
  rintro z ⟨x, hx, rfl⟩
  exact ⟨x, h hx, rfl⟩

/-- The restriction of the actual solution function. -/
def restrictSolution {r : ℕ} (S : Finset ℂ)
    (A : Matrix (Fin r) (Fin r) RationalFunctions)
    {U V : Opens (puncturedLine S)} (h : V ≤ U) :
    solutionSections S A U →ₗ[ℂ] solutionSections S A V := by
  classical
  refine
    { toFun := fun s ↦ ⟨fun z ↦ if z ∈ ambientOpen S V then s.1 z else 0, ?_⟩
      map_add' := ?_
      map_smul' := ?_ }
  · constructor
    · intro z hz; simp [hz]
    · intro z hz i
      have hd := (s.2.2 z (ambientOpen_mono S h hz) i).mono (ambientOpen_mono S h)
      convert hd.congr
        (f₁ := fun t ↦ (if t ∈ ambientOpen S V then s.1 t else 0) i)
        (fun t ht ↦ by simp [ht]) (by simp [hz]) using 1
      simp [hz]
  · intro s t
    apply Subtype.ext
    funext z
    by_cases hz : z ∈ ambientOpen S V <;> simp [hz]
  · intro c s
    apply Subtype.ext
    funext z
    by_cases hz : z ∈ ambientOpen S V <;> simp [hz]

/-- The actual presheaf of holomorphic solutions of `s'=A(z)s`. -/
def solutionPresheaf {r : ℕ} (S : Finset ℂ)
    (A : Matrix (Fin r) (Fin r) RationalFunctions) :
    (Opens (puncturedLine S))ᵒᵖ ⥤ ModuleCat.{0} ℂ where
  obj U := ModuleCat.of ℂ (solutionSections S A U.unop)
  map h := ModuleCat.ofHom (restrictSolution S A h.unop.le)
  map_id U := by
    ext s z
    by_cases hz : z ∈ ambientOpen S U.unop
    · simp [restrictSolution, hz]
    · simp [restrictSolution, hz, s.2.1 z hz]
  map_comp {U V W} f g := by
    ext s z
    by_cases hz : z ∈ ambientOpen S W.unop
    · have hv := ambientOpen_mono S g.unop.le hz
      simp [restrictSolution, hz, hv]
    · simp [restrictSolution, hz]

/-- The actual solution sheaf, obtained from these explicit sections. -/
def solutionSheaf {r : ℕ} (S : Finset ℂ)
    (A : Matrix (Fin r) (Fin r) RationalFunctions) :
    TopCat.Sheaf (ModuleCat.{0} ℂ) (puncturedLine S) :=
  (presheafToSheaf (Opens.grothendieckTopology (puncturedLine S))
    (ModuleCat.{0} ℂ)).obj (solutionPresheaf S A)

/-- The actual map from solution presheaf sections into the solution sheaf. -/
def solutionUnit {r : ℕ} (S : Finset ℂ)
    (A : Matrix (Fin r) (Fin r) RationalFunctions) :
    solutionPresheaf S A ⟶ (solutionSheaf S A).obj :=
  (sheafificationAdjunction (Opens.grothendieckTopology (puncturedLine S))
    (ModuleCat.{0} ℂ)).unit.app (solutionPresheaf S A)

/-- The actual horizontal rational gauge equation for an interconnection
map `G : (δ-A) → (δ-B)`. -/
def HorizontalMatrix (δ : RationalDerivative) {r s : ℕ}
    (A : Matrix (Fin r) (Fin r) RationalFunctions)
    (B : Matrix (Fin s) (Fin s) RationalFunctions)
    (G : Matrix (Fin s) (Fin r) RationalFunctions) : Prop :=
  ∀ i j, δ.derivation (G i j) = (B * G - G * A) i j

/-- A sheaf morphism is normalized by the actual evaluated rational matrix
on every solution section before sheafification. -/
def InducedByMatrix {r s : ℕ} (S : Finset ℂ)
    (A : Matrix (Fin r) (Fin r) RationalFunctions)
    (B : Matrix (Fin s) (Fin s) RationalFunctions)
    (φ : solutionSheaf S A ⟶ solutionSheaf S B)
    (G : Matrix (Fin s) (Fin r) RationalFunctions) : Prop :=
  ∀ (U : Opens (puncturedLine S)) (v : solutionSections S A U),
    ∃ w : solutionSections S B U,
      (∀ z ∈ ambientOpen S U, ∀ i, w.1 z i = ((evaluated G z).mulVec (v.1 z)) i) ∧
      φ.hom.app (op U) ((solutionUnit S A).app (op U) v) =
        (solutionUnit S B).app (op U) w

end MathlibExt.AlgebraicGeometry.RegularSingularConnections
