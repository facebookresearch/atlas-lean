/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.ModularForms.HeckeAlgebra

@[expose] public section

/-- exactSource consumer: the original binders apply verbatim. -/
example {N : ℕ} (k : ℤ) {p q : ℕ} (hp : p.Prime) (hpN : ¬ p ∣ N)
    (hq : q.Prime) (hqN : ¬ q ∣ N) :
    Commute (CuspForm.heckeTLin k hp hpN) (CuspForm.heckeTLin k hq hqN) :=
  CuspForm.heckeTLin_comm k hp hpN hq hqN

/-- exactSource consumer: the original binders apply verbatim. -/
example {N : ℕ} [NeZero N] (k : ℤ) {p q : ℕ} (hp : p.Prime) (hpN : ¬ p ∣ N) (hqN : q ∣ N) :
    Commute (CuspForm.heckeTLin k hp hpN) (CuspForm.heckeULin k hqN) :=
  CuspForm.heckeTLin_heckeULin_comm k hp hpN hqN

/-- exactSource consumer: the original binders apply verbatim. -/
example {N : ℕ} [NeZero N] (k : ℤ) {p q : ℕ} (hpN : p ∣ N) (hqN : q ∣ N) :
    Commute (CuspForm.heckeULin k hpN) (CuspForm.heckeULin k hqN) :=
  CuspForm.heckeULin_comm k hpN hqN

/-- exactSource consumer: the original binders apply verbatim. -/
example {N : ℕ} [NeZero N] {k : ℤ} (hk : 1 ≤ k) {S : Set ℕ}
    {t : Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) k)}
    (ht : t ∈ CuspForm.heckeAlgebra N k S) {f : CuspForm (CongruenceSubgroup.Gamma0 N) k}
    (hf : f ∈ CuspForm.intLattice N k) : t f ∈ CuspForm.intLattice N k :=
  CuspForm.mem_intLattice_of_mem_heckeAlgebra hk ht hf

/-- The Hecke algebra is a commutative ring: `T_ℓ` and `U_q` commute inside it. -/
example {N : ℕ} [NeZero N] (k : ℤ) (S : Set ℕ) {ℓ q : ℕ} (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N)
    (hℓS : ℓ ∉ S) (hq : q.Prime) (hqN : q ∣ N) (hqS : q ∉ S) :
    (CuspForm.heckeAlgebra.T hℓ hℓN hℓS : CuspForm.heckeAlgebra N k S) *
        CuspForm.heckeAlgebra.U hq hqN hqS =
      CuspForm.heckeAlgebra.U hq hqN hqS * CuspForm.heckeAlgebra.T hℓ hℓN hℓS :=
  mul_comm _ _

/-- Removing primes from `S` can only enlarge the Hecke algebra. -/
example {N : ℕ} [NeZero N] (k : ℤ) :
    CuspForm.heckeAlgebra N k {2} ≤ CuspForm.heckeAlgebra N k ∅ :=
  CuspForm.heckeAlgebra_mono (Set.empty_subset _)
