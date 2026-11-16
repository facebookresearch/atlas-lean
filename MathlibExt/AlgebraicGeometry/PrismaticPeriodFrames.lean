/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.PrismaticFilteredTwists
public import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Period frames fixed by the actual Teichmuller-root conormal generators

The xi generator is the literal sum of the p powers of phi^{-1}(epsilon).
The compatible conormal basis has the actual product
phi(xi) ... phi^r(xi) at its rth component. Its map from the scalar module
is computed, and being an isomorphism is a separate construction/proof
request. No freely chosen line basis defines Frobenius.

These are the standard root-of-unity frames in BMS18,
arXiv:1602.03148v3, Example 4.24: phi(e)=e/phi(xi).
The p-divided conormal transition and generator congruence are retained
literally. Root extraction and period-frame existence are source
construction inputs, independent of the nearby-cycle theorem.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.PrismaticPeriodFrames

open CategoryTheory CategoryTheory.Limits
open MathlibExt.RingTheory MathlibExt.RingTheory.BoundedPrisms
open PrismaticBreuilKisinSeeds
open scoped BigOperators

variable (p : ℕ) [Fact p.Prime] (P : Prism.{0} p)
  (perfect : Function.Bijective (DeltaRing.frobenius p P.ring))

/-- The actual perfect-prism inverse Frobenius. -/
def inversePhi : P.ring →+* P.ring :=
  (RingEquiv.ofBijective (DeltaRing.frobenius p P.ring) perfect).symm.toRingHom

/-- The real cyclotomic xi polynomial in phi^{-1}(epsilon). -/
def xi (epsilon : P.ring) : P.ring :=
  ∑ k ∈ Finset.range p, (inversePhi p P perfect epsilon) ^ k

/-- Actual normalized period-generator data, with no free xi element. -/
structure Generator where
  epsilon : P.ring
  unit : IsUnit epsilon
  teichmuller : DeltaRing.frobenius p P.ring epsilon = epsilon ^ p
  theta : Ideal.Quotient.mk P.ideal epsilon = 1
  ideal : P.ideal = Ideal.span {xi p P perfect epsilon}
  congruence : ∀ n : ℕ,
    phiPower p P (n + 2) (xi p P perfect epsilon) - (p : P.ring) ∈ periodIdeal p P n

namespace Generator

variable {p P perfect} (G : Generator p P perfect)

/-- The actual xi of the given root system. -/
abbrev value : P.ring := xi p P perfect G.epsilon

/-- Every finite conormal generator is the actual successive Frobenius product. -/
def product : ℕ → P.ring
  | 0 => phiPower p P 1 G.value
  | n + 1 => product n * phiPower p P (n + 2) G.value

/-- These are genuine elements of the source's period ideals. -/
theorem product_mem (n : ℕ) : G.product n ∈ periodIdeal p P n := by
  have hd : G.value ∈ P.ideal := by
    rw [G.ideal]
    exact Ideal.subset_span (Set.mem_singleton G.value)
  induction n with
  | zero => exact Ideal.mem_map_of_mem _ hd
  | succ n ih => exact Ideal.mul_mem_mul ih (Ideal.mem_map_of_mem _ hd)

variable (T : DividedConormalTower p P)

/-- The computed compatible conormal vector, with the actual p-division relation. -/
def vector : T.SeedModule :=
  ⟨fun n ↦ (periodIdeal p P n).toCotangent ⟨G.product n, G.product_mem n⟩, by
    intro n
    apply T.p_regular n
    dsimp only
    rw [T.normalization]
    change (periodIdeal p P n).toCotangent
      ⟨G.product (n + 1), periodIdeal_step_le p P n (G.product_mem (n + 1))⟩ =
        (p : P.ring) • (periodIdeal p P n).toCotangent ⟨G.product n, G.product_mem n⟩
    rw [← map_smul]
    apply (Ideal.toCotangent_eq _).mpr
    change G.product (n + 1) - (p : P.ring) * G.product n ∈ (periodIdeal p P n) ^ 2
    rw [pow_two]
    convert Ideal.mul_mem_mul (G.product_mem n) (G.congruence n) using 1
    simp only [product]
    ring⟩

end Generator

/-- The period-frame map is computed from the conormal vector, not chosen independently. -/
def frameHom (L : ClassicalSeed p P) (G : Generator p P perfect) :
    ModuleCat.of P.ring P.ring ⟶ L.module :=
  ModuleCat.ofHom
    { toFun a := a • G.vector L.tower
      map_add' a b := add_smul a b _
      map_smul' a b := mul_smul a b _ }

/-- A source period frame records only invertibility of that fixed map. -/
structure Frame (L : ClassicalSeed p P) where
  generator : Generator p P perfect
  [isIso : IsIso (frameHom p P perfect L generator)]

/-- The actual period module frame, with its fixed source generators. -/
def Frame.iso {L : ClassicalSeed p P} (F : Frame p P perfect L) :
    ModuleCat.of P.ring P.ring ≅ L.module := by
  letI := F.isIso
  exact asIso (frameHom p P perfect L F.generator)

end MathlibExt.AlgebraicGeometry.PrismaticPeriodFrames
