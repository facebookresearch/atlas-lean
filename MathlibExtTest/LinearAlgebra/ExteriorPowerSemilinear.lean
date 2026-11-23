/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.LinearAlgebra.ExteriorPowerSemilinear
import Mathlib.Data.ZMod.Basic

/-! # Tests for semilinear base change of exterior powers

Generator normalization, identity and composition laws, degree zero, a concrete base change along
the nonidentity ring map `ℤ → ZMod 3`, and the zero ring.
-/

open ExteriorAlgebra

namespace MathlibExtTest.LinearAlgebra.ExteriorPowerSemilinear

section General

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
  {M N P : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module S N]
  [AddCommGroup P] [Module T P] (φ : R →+* S) (ψ : S →+* T) (u : M →ₛₗ[φ] N) (w : N →ₛₗ[ψ] P)

example (m : M) : mapₛₗ φ u (ι R m) = ι S (u m) := by simp

example (r : R) : mapₛₗ φ u (algebraMap R _ r) = algebraMap S _ (φ r) := by simp

example (r : R) (x : ExteriorAlgebra R M) : mapₛₗ φ u (r • x) = φ r • mapₛₗ φ u x :=
  mapₛₗ_smul φ u r x

example (n : ℕ) (v : Fin n → M) :
    powMapₛₗ n φ u (exteriorPower.ιMulti R n v) = exteriorPower.ιMulti S n fun i => u (v i) := by
  simp

/-- Base change along the identity is the identity, in every degree. -/
example (n : ℕ) (x : ⋀[R]^n M) : powMapₛₗ n (RingHom.id R) LinearMap.id x = x :=
  powMapₛₗ_eq_self n _ (fun _ => rfl) (fun _ => rfl) x

/-- Base change is compatible with composition. -/
example (n : ℕ) (v : M →ₛₗ[ψ.comp φ] P) (hv : ∀ m, v m = w (u m)) (x : ⋀[R]^n M) :
    powMapₛₗ n (ψ.comp φ) v x = powMapₛₗ n ψ w (powMapₛₗ n φ u x) :=
  powMapₛₗ_eq_comp n u w v (fun _ => rfl) hv x

/-- In degree zero base change sends `1` to `1`. -/
example : powMapₛₗ 0 φ u ⟨1, one_mem_exteriorPower⟩ = ⟨1, one_mem_exteriorPower⟩ :=
  Subtype.ext (map_one _)

end General

/-- Reduction modulo `3`, as a semilinear map `ℤ → ZMod 3` along `ℤ → ZMod 3`. -/
def castₛₗ : ℤ →ₛₗ[Int.castRingHom (ZMod 3)] ZMod 3 where
  toFun n := n
  map_add' := Int.cast_add
  map_smul' r n := by simp

/-- Base change along the nonidentity ring map `ℤ → ZMod 3` reduces the vectors modulo `3`. -/
example : powMapₛₗ 1 (Int.castRingHom (ZMod 3)) castₛₗ (exteriorPower.ιMulti ℤ 1 ![5]) =
    exteriorPower.ιMulti (ZMod 3) 1 ![2] := by
  rw [powMapₛₗ_ιMulti]
  congr 1
  ext i
  fin_cases i
  decide

/-- Base change along a nonidentity ring map is semilinear: scalars are reduced modulo `3`. -/
example (x : ⋀[ℤ]^1 ℤ) :
    powMapₛₗ 1 (Int.castRingHom (ZMod 3)) castₛₗ ((4 : ℤ) • x) =
      (1 : ZMod 3) • powMapₛₗ 1 (Int.castRingHom (ZMod 3)) castₛₗ x := by
  rw [map_smulₛₗ]
  congr 1

/-- Base change into an exterior power over the zero ring is zero. -/
example {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] (φ : R →+* PUnit)
    (u : M →ₛₗ[φ] PUnit) (n : ℕ) (x : ⋀[R]^n M) : powMapₛₗ n φ u x = 0 :=
  (Module.subsingleton PUnit _).elim _ _

end MathlibExtTest.LinearAlgebra.ExteriorPowerSemilinear
