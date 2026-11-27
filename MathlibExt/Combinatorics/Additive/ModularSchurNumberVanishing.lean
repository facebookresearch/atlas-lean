/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Additive.ModularSchurNumbers
import all MathlibExt.Combinatorics.Additive.ModularSchurNumbers

/-!
# Vanishing of modular Schur numbers

A multiple of the modulus cannot belong to a sum-free color class, so admissible lengths
are bounded. Whether the singleton `{1}` is sum-free determines whether any positive
length is admissible.

## References

* Jourdan D'orville, Kai An Sim, Kok Bin Wong, and Chee Kit Ho,
  *Modular Generalizations of Schur Numbers*, INTEGERS 25 (2025), Article A62,
  pp. 1–19, §1.1, equation (1), and Corollaries 1 and 2.
* Jonathan Chappelon, María Pastora Revuelta Marchena, and María Isabel Sanz Domínguez,
  *Modular Schur numbers*, Electronic Journal of Combinatorics 20(2) (2013), #P61,
  pp. 1–26, §1.1, equation (2), and §2 (the bound and the singleton argument for moduli 2 and 3).
* David M. Burton, *Elementary Number Theory*, 7th ed., McGraw-Hill, 2011, §4.4
  (the linear congruence criterion cited in the source paper's route to Corollary 1).
-/

set_option autoImplicit false

namespace MetaMathlibExt

-- Keep the source's positivity hypothesis on `l`, although the partition argument does not use it.
set_option linter.unusedVariables false in
/-- **Vanishing of modular Schur numbers.** Let $m$, $k$ and $l$ be positive integers. The
generalized Schur number $S_m(k, l)$, the largest $n$ such that $\{1, \dots, n\}$ admits a
partition into $k$ classes that are $l$-sum-free modulo $m$, equals $0$ if and only if
$l \equiv 1 \pmod{m}$.

Source: Jourdan D'orville, Kai An Sim, Kok Bin Wong, and Chee Kit Ho, *Modular
Generalizations of Schur Numbers*, INTEGERS 25 (2025), Article A62, Corollary 2
(`integers-2025-A62-cor-2`). -/
public theorem modularSchurNumber_eq_zero_iff (m k l : ℕ) (hm : 0 < m) (hk : 0 < k)
    (hl : 0 < l) : modularSchurNumber m k l = 0 ↔ l ≡ 1 [MOD m] := by
  constructor
  · intro hz
    by_contra h
    have hb : BddAbove {n : ℕ | HasSumFreePartitionMod m k l n} := by
      refine ⟨m - 1, ?_⟩
      intro n hn
      by_contra! hnm
      obtain ⟨c, hc⟩ := hn
      have hmem : (m : ℤ) ∈ {x : ℤ | ∃ a : ℕ, 1 ≤ a ∧ a ≤ n ∧ c a = c m ∧ x = a} :=
        ⟨m, hm, by omega, rfl, rfl⟩
      exact not_isSumFreeMod_of_dvd_mem m l hmem (dvd_refl _) (hc (c m))
    have hone : HasSumFreePartitionMod m k l 1 := by
      apply modularSchurNumber_two_mul.partition_of_not_modEq hk hk
      intro a ha ha'
      have ha₁ : a = 1 := le_antisymm ha' ha
      simpa only [ha₁, Nat.mul_one] using h
    have hle : 1 ≤ modularSchurNumber m k l := le_csSup hb hone
    omega
  · intro h
    apply IsGreatest.csSup_eq
    constructor
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
      exact hasSumFreePartitionMod_zero m j l
    · intro n hn
      have hlt := modularSchurNumber_two_mul.lt_of_modEq hn (by decide : 0 < (1 : ℕ))
        (by simpa only [Nat.mul_one] using h)
      exact Nat.le_of_lt_succ hlt

end MetaMathlibExt
