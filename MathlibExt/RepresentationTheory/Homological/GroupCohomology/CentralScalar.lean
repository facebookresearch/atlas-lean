/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Nat.Prime.Defs

/-!
# Low-degree cohomology vanishes when a central element acts by a scalar

Let `A` be a `k`-linear representation of a group `G`, and let `z ∈ G` be central and act on `A`
as multiplication by `c ∈ k` with `c - 1` a unit. Then `H⁰(G, A) = 0`
(`groupCohomology.isZero_H0_of_central_smul`) and `H¹(G, A) = 0`
(`groupCohomology.isZero_H1_of_central_smul`).

For a commutative ring `R` in which `2` is a unit, the homothety `2 · 1` of `GL_n(R)` acts on
`Rⁿ` by `2`, with `2 - 1 = 1`, so `H⁰(GL_n(R), Rⁿ) = H¹(GL_n(R), Rⁿ) = 0`
(`Matrix.GeneralLinearGroup.isZero_H0_and_H1_stdRep`); in particular for
`GL₂(ℤ/pℤ)` acting on `(ℤ/pℤ)²`, `p` an odd prime
(`Matrix.GeneralLinearGroup.isZero_H0_and_H1_stdRep_zmod`). These are the degrees `n = 0, 1`
of the vanishing `Hⁿ(𝒢, E_p) = 0` of Gross's Proposition 9.1, with `𝒢 ≅ GL₂(ℤ/pℤ)` acting on
`E_p ≅ (ℤ/pℤ)²`.

## Proof

`H⁰`: an invariant `x` satisfies `x = z • x = c • x`, so `(c - 1) • x = 0` and `x = 0`.
`H¹`: for a `1`-cocycle `f`, expanding `f (z g) = f (g z)` gives
`(c - 1) • f g = g • f z - f z`, so `f` is the coboundary of `(c - 1)⁻¹ • f z`. Gross's proof
(due to Serre) instead uses the Hochschild–Serre spectral sequence for the central subgroup
of homotheties, which gives all degrees.

## References

* B. H. Gross, *Kolyvagin's work on modular elliptic curves*, in *L-functions and arithmetic*
  (Durham, 1989), London Math. Soc. Lecture Note Ser. 153, Cambridge Univ. Press, 1991,
  235–256: §9, Proposition 9.1 and its proof, p. 250 ("We have `Hⁿ(𝒢, E_p) = 0` for all
  `n ≥ 0`.").
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory

namespace groupCohomology

variable {k G : Type} [CommRing k] [Group G] (A : Rep k G)

/-- **`H⁰` vanishes when an element acts by a scalar `c` with `c - 1` a unit.** If some `z ∈ G`
acts on `A` as multiplication by `c ∈ k` and `c - 1` is a unit of `k`, then `H⁰(G, A) = 0`. -/
theorem isZero_H0_of_central_smul (z : G) (c : k) (hc : IsUnit (c - 1))
    (hρ : ∀ v, A.ρ z v = c • v) : Limits.IsZero (H0 A) := by
  have : Subsingleton A.ρ.invariants := by
    refine subsingleton_of_forall_eq 0 fun x => ?_
    ext
    have h := (Representation.mem_invariants A.ρ x).1 x.2 z
    rw [hρ] at h
    have h' : (c - 1) • (x : A) = 0 := by rw [sub_smul, one_smul, h, sub_self]
    obtain ⟨u, hu⟩ := hc
    have h'' : (↑u⁻¹ : k) • ((c - 1) • (x : A)) = 0 := by rw [h', smul_zero]
    rwa [← hu, smul_smul, Units.inv_mul, one_smul] at h''
  exact Limits.IsZero.of_iso (ModuleCat.isZero_of_subsingleton _) (H0Iso A)

/-- **`H¹` vanishes when a central element acts by a scalar `c` with `c - 1` a unit.** If
`z ∈ G` commutes with every element of `G` and acts on `A` as multiplication by `c ∈ k`, and
`c - 1` is a unit of `k`, then `H¹(G, A) = 0`: every `1`-cocycle is the coboundary of
`(c - 1)⁻¹ • f z`. -/
theorem isZero_H1_of_central_smul (z : G) (hz : ∀ g, z * g = g * z) (c : k)
    (hc : IsUnit (c - 1)) (hρ : ∀ v, A.ρ z v = c • v) : Limits.IsZero (H1 A) := by
  have : Subsingleton (H1 A) := by
    refine subsingleton_of_forall_eq 0 fun x => ?_
    induction x using H1_induction_on with
    | _ f =>
      rw [H1π_eq_zero_iff]
      have hf := (mem_cocycles₁_iff (f : G → A)).1 f.2
      obtain ⟨u, hu⟩ := hc
      refine ⟨(↑u⁻¹ : k) • (f : G → A) z, funext fun g => ?_⟩
      rw [d₀₁_hom_apply, map_smul, ← smul_sub]
      have h1 := hf z g
      rw [hz g, hf g z, hρ] at h1
      have key : (c - 1) • (f : G → A) g = A.ρ g ((f : G → A) z) - (f : G → A) z := by
        rw [sub_smul, one_smul]
        exact sub_eq_sub_iff_add_eq_add.2 h1.symm
      rw [← key, ← hu, smul_smul, Units.inv_mul, one_smul]
  exact ModuleCat.isZero_of_subsingleton _

end groupCohomology

namespace Matrix.GeneralLinearGroup

/-- The **standard representation** of `GL_n(R)` on `Rⁿ = n → R`, by `g • v = g *ᵥ v`. -/
noncomputable def stdRep (n : Type) [Fintype n] [DecidableEq n] (R : Type) [CommRing R] :
    Representation R (GL n R) (n → R) :=
  (Units.coeHom _).comp toLin.toMonoidHom

/-- The standard representation acts by matrix-vector multiplication. -/
theorem stdRep_apply (n : Type) [Fintype n] [DecidableEq n] (R : Type) [CommRing R]
    (g : GL n R) (v : n → R) : stdRep n R g v = (g : Matrix n n R).mulVec v :=
  rfl

/-- **`H⁰` and `H¹` of `GL_n(R)` on `Rⁿ` vanish when `2` is a unit of `R`.** For a commutative
ring `R` with `2 ∈ Rˣ` and the standard representation of `GL_n(R)` on `n → R`, `H⁰` and `H¹`
are zero: the central homothety `2 · 1` acts by `2`, and `2 - 1 = 1`. -/
theorem isZero_H0_and_H1_stdRep (n : Type) [Fintype n] [DecidableEq n] (R : Type)
    [CommRing R] (h2 : IsUnit (2 : R)) :
    Limits.IsZero (groupCohomology.H0 (Rep.of (stdRep n R))) ∧
      Limits.IsZero (groupCohomology.H1 (Rep.of (stdRep n R))) := by
  obtain ⟨u, hu⟩ := h2
  let z : GL n R := scalar n u
  have hz : ∀ g, z * g = g * z := fun g => by
    ext i j
    simp [z, scalar, mul_comm]
  have hρ : ∀ v, (Rep.of (stdRep n R)).ρ z v = (2 : R) • v := fun v => by
    simp [z, stdRep_apply, scalar, hu]
  have hc : IsUnit ((2 : R) - 1) := by norm_num
  exact ⟨groupCohomology.isZero_H0_of_central_smul _ z 2 hc hρ,
    groupCohomology.isZero_H1_of_central_smul _ z hz 2 hc hρ⟩

/-- **`H⁰(GL₂(ℤ/pℤ), (ℤ/pℤ)²) = H¹(GL₂(ℤ/pℤ), (ℤ/pℤ)²) = 0` for an odd prime `p`**, for the
standard representation of `GL₂(ℤ/pℤ)` on `Fin 2 → ℤ/pℤ`. -/
theorem isZero_H0_and_H1_stdRep_zmod (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    Limits.IsZero (groupCohomology.H0 (Rep.of (stdRep (Fin 2) (ZMod p)))) ∧
      Limits.IsZero (groupCohomology.H1 (Rep.of (stdRep (Fin 2) (ZMod p)))) := by
  refine isZero_H0_and_H1_stdRep (Fin 2) (ZMod p) (isUnit_iff_ne_zero.2 fun h => hp ?_)
  have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at h'
  exact (Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).1 h'

end Matrix.GeneralLinearGroup

end
