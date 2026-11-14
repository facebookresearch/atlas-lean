/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.RingTheory.LaurentSeries
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import MathlibExt.Geometry.LimitingHodgeStructures
public import MathlibExt.Algebra.Homology.TwoTermComplex

/-!
# The completed unipotent curve Hodge-module lattice and its filtration

The coefficient ring is `ℂ[[t]]` inside the actual field `ℂ((t))`. The
Deligne lattice, logarithmic residue, connection, generated minimal
differential module and Hodge filtration are all fixed constructions.
Taylor coefficients of actual holomorphic sections of the untwisted
period extension specify the completed Hodge lattice.

This models the formal boundary of the pure Hodge-module extension of a
polarized unipotent variation. It does not declare a category of arbitrary
mixed Hodge modules. With variation weight `w`, the curve Hodge module has
weight `w+1`; the limiting variation uses monodromy center `w`.

The left differential-module filtration is
`F_p M = Σ_i ∇^i(F_{p-i} V^(-1,0])`, with `F_p V = F^(-p) V`.
The residue has eigenvalue zero, so `V^(-1,0]` is the unipotent Deligne
lattice. In the period-deck convention of the input, the connection is
`d + (log T)/(2πi) dt/t` and its parallel-transport monodromy is `T⁻¹`.

Sources: M. Saito, *Modules de Hodge polarisables*, Publ. RIMS 24 (1988),
§3.2; C. Schnell, https://arxiv.org/abs/1405.3096, §§11 and 18,
especially the lattice and filtration formulas in Part 1 of §18.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.HodgeModuleCurveExtension

open CategoryTheory CategoryTheory.Limits
open MathlibExt.Geometry.RationalHodgeStructures
open MathlibExt.Geometry.LimitingHodgeStructures

/-- The actual completed holomorphic local ring. -/
abbrev LocalPowerSeries := PowerSeries ℂ

/-- Its actual meromorphic Laurent series field. -/
abbrev LocalMeromorphicSeries := LaurentSeries ℂ

/-- The actual coefficient and power-series embeddings form the required
scalar tower, including the two existing descriptions of the Laurent
coefficient algebra. -/
instance coefficientScalarTower : IsScalarTower ℂ LocalPowerSeries LocalMeromorphicSeries :=
  IsScalarTower.of_algebraMap_smul
    (R := ℂ) (A := LocalPowerSeries) (M := LocalMeromorphicSeries) fun c v ↦ by
      change HahnSeries.ofPowerSeries ℤ ℂ (PowerSeries.C c) * v = c • v
      rw [HahnSeries.ofPowerSeries_C]
      exact HahnSeries.C_mul_eq_smul

/-- Inclusion of the finite free Deligne lattice into the meromorphic
connection space, using the actual power-to-Laurent map. -/
def latticeEmbedding (r : ℕ) :
    (Fin r → LocalPowerSeries) →ₗ[LocalPowerSeries] (Fin r → LocalMeromorphicSeries) where
  toFun := fun v i ↦ algebraMap LocalPowerSeries LocalMeromorphicSeries (v i)
  map_add' := by intro v w; ext i; simp
  map_smul' := by intro a v; ext i; simp [Algebra.smul_def]

/-- The full canonical lattice `ℂ[[t]]^r`. -/
def deligneLattice (r : ℕ) : Submodule LocalPowerSeries (Fin r → LocalMeromorphicSeries) :=
  LinearMap.range (latticeEmbedding r)

variable {V : ModuleCat.{0} ℚ} (C : RationalComplexification V) {r : ℕ}
  (e : C.complexSpace ≃ₗ[ℂ] EuclideanSpace ℂ (Fin r)) {w : ℤ}
  (H : PolarizedPeriodVariation C e w) (b : ℕ)

/-- The actual logarithmic residue matrix, in the fixed period coordinates. -/
def residueMatrix : Matrix (Fin r) (Fin r) ℂ := fun i j ↦
  (e (complexLog C e H b (e.symm (EuclideanSpace.single j 1))) i) /
    (2 * Real.pi * Complex.I)

/-- The formal connection is the actual Laurent derivative plus the
actual logarithmic residue divided by the actual coordinate `t`. -/
def formalConnection : Module.End ℂ (Fin r → LocalMeromorphicSeries) where
  toFun := fun v i ↦ LaurentSeries.derivative ℂ (v i) +
    (algebraMap LocalPowerSeries LocalMeromorphicSeries PowerSeries.X)⁻¹ *
      ∑ j : Fin r, algebraMap ℂ LocalMeromorphicSeries (residueMatrix C e H b i j) * v j
  map_add' := by
    intro v u
    funext i
    simp [mul_add, Finset.sum_add_distrib]
    ring
  map_smul' := by
    intro c v
    funext i
    simp only [Pi.smul_apply, map_smul, smul_add]
    congr 1
    simp_rw [← HahnSeries.C_mul_eq_smul]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    simp [mul_left_comm, mul_comm]

/-- The least actual `ℂ[[t]]` submodule containing the Deligne lattice and
stable under the fixed connection. This is its generated minimal
differential module, with no free module carrier supplied. -/
def minimalModule : Submodule LocalPowerSeries (Fin r → LocalMeromorphicSeries) :=
  sInf {P | deligneLattice r ≤ P ∧
    ∀ v, v ∈ P → formalConnection C e H b v ∈ P}

theorem lattice_le_minimal : deligneLattice r ≤ minimalModule C e H b :=
  le_sInf fun _ hP ↦ hP.1

theorem connection_mem_minimal {v : Fin r → LocalMeromorphicSeries}
    (hv : v ∈ minimalModule C e H b) :
    formalConnection C e H b v ∈ minimalModule C e H b := by
  rw [minimalModule, Submodule.mem_sInf] at hv ⊢
  intro P hP
  exact hP.2 v (hv P hP)

/-- The same concrete module with its underlying complex linear structure. -/
abbrev minimalComplexModule := (minimalModule C e H b).restrictScalars ℂ

/-- Restriction of the actual connection to the constructed minimal module. -/
def minimalConnection : Module.End ℂ (minimalComplexModule C e H b) :=
  (formalConnection C e H b).restrict fun _ hv ↦ connection_mem_minimal C e H b hv

/-- The actual formal de Rham complex of the minimal extension in degrees
zero and one. The curve perverse normalization is its shift `[1]`. -/
def minimalDeRhamComplex : CochainComplex (ModuleCat.{0} ℂ) ℕ :=
  MathlibExt.Algebra.Homology.twoTermComplex
    (ModuleCat.ofHom (X := ModuleCat.of ℂ (minimalComplexModule C e H b))
      (Y := ModuleCat.of ℂ (minimalComplexModule C e H b)) (minimalConnection C e H b))

/-- Taylor series of an actual holomorphic coordinate section. -/
def taylorSection (s : ℂ → EuclideanSpace ℂ (Fin r)) : Fin r → LocalPowerSeries :=
  fun i ↦ PowerSeries.mk fun n ↦ iteratedDeriv n (fun t ↦ s t i) 0 / (n.factorial : ℂ)

/-- The completed Hodge lattice generated by actual holomorphic germs of
the fixed untwisted extension. The sign converts decreasing Hodge `F^p`
to the increasing left differential-module filtration `F_p`. -/
def hodgeLattice (E : PeriodExtension C e H b) (p : ℤ) :
    Submodule LocalPowerSeries (Fin r → LocalMeromorphicSeries) :=
  Submodule.span LocalPowerSeries {v | ∃ ε : ℝ, 0 < ε ∧
    Metric.ball 0 ε ⊆ {t : ℂ | ‖t‖ < 1} ∧
    ∃ s : ℂ → EuclideanSpace ℂ (Fin r),
      DifferentiableOn ℂ s (Metric.ball 0 ε) ∧
      (∀ t ∈ Metric.ball 0 ε, e.symm (s t) ∈ E.F t (-p)) ∧
      v = latticeEmbedding r (taylorSection s)}

theorem hodgeLattice_le_lattice (E : PeriodExtension C e H b) (p : ℤ) :
    hodgeLattice C e H b E p ≤ deligneLattice r := by
  apply Submodule.span_le.mpr
  rintro v ⟨ε, hε, hεU, s, hs, hsF, rfl⟩
  exact ⟨taylorSection s, rfl⟩

/-- The Hodge filtration of the generated minimal extension, as the
actual module span of iterated connection images of its Hodge lattice. -/
def hodgeFiltration (E : PeriodExtension C e H b) (p : ℤ) :
    Submodule LocalPowerSeries (Fin r → LocalMeromorphicSeries) :=
  Submodule.span LocalPowerSeries {v | ∃ i : ℕ, ∃ u,
    u ∈ hodgeLattice C e H b E (p - i) ∧
      v = (formalConnection C e H b)^[i] u}

/-- The actual module generated by the connection image of a submodule. -/
def connectionImage (P : Submodule LocalPowerSeries (Fin r → LocalMeromorphicSeries)) :
    Submodule LocalPowerSeries (Fin r → LocalMeromorphicSeries) :=
  Submodule.span LocalPowerSeries {v | ∃ u, u ∈ P ∧ v = formalConnection C e H b u}

/-- Goodness for the actual left differential-module filtration: finite
steps, a lower bound, exhaustion, order compatibility and eventual
generation by the order-one connection operator. -/
structure GoodHodgeFiltration (E : PeriodExtension C e H b) : Prop where
  monotone : Monotone (hodgeFiltration C e H b E)
  bounded_below : ∃ p₀ : ℤ, ∀ p < p₀, hodgeFiltration C e H b E p = ⊥
  finite : ∀ p : ℤ, (hodgeFiltration C e H b E p).FG
  exhaustive : (⨆ p : ℤ, hodgeFiltration C e H b E p) = minimalModule C e H b
  differential : ∀ p : ℤ,
    connectionImage C e H b (hodgeFiltration C e H b E p) ≤
      hodgeFiltration C e H b E (p + 1)
  generated : ∃ p₀ : ℤ, ∀ p ≥ p₀,
    hodgeFiltration C e H b E (p + 1) =
      hodgeFiltration C e H b E p ⊔
        connectionImage C e H b (hodgeFiltration C e H b E p)

theorem hodgeFiltration_le_minimal (E : PeriodExtension C e H b) (p : ℤ) :
    hodgeFiltration C e H b E p ≤ minimalModule C e H b := by
  apply Submodule.span_le.mpr
  rintro v ⟨i, u, hu, rfl⟩
  have huM := (lattice_le_minimal C e H b)
    ((hodgeLattice_le_lattice C e H b E (p - i)) hu)
  clear hu
  induction i with
  | zero => simpa using huM
  | succ i hi =>
      rw [Function.iterate_succ_apply']
      exact connection_mem_minimal C e H b hi

/-- Evaluation at the closed point by the actual zero Laurent coefficient,
transported through the fixed complex period coordinates. -/
def specialization : (Fin r → LocalMeromorphicSeries) →ₗ[ℂ] C.complexSpace :=
  e.symm.toLinearMap.comp
    ((WithLp.linearEquiv 2 ℂ (Fin r → ℂ)).symm.toLinearMap.comp
      ({ toFun := fun v i ↦ (v i).coeff 0
         map_add' := by intro v u; ext i; simp
         map_smul' := by intro c v; ext i; simp } :
        (Fin r → LocalMeromorphicSeries) →ₗ[ℂ] (Fin r → ℂ)))

end MathlibExt.AlgebraicGeometry.HodgeModuleCurveExtension
