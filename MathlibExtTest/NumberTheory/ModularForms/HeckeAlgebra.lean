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

/-- The primes in `S` are left out: away from every prime, the Hecke algebra is the bottom
`ℤ`-subalgebra, the image of the scalars. That image is the zero ring when there are no
nonzero cusp forms, as in odd weight. -/
example {N : ℕ} [NeZero N] (k : ℤ) : CuspForm.heckeAlgebra N k Set.univ = ⊥ := by
  have h : CuspForm.heckeGenerators N k Set.univ = ∅ :=
    Set.eq_empty_of_forall_notMem fun _ hT => by
      rcases hT with ⟨ℓ, -, -, hℓ, -⟩ | ⟨q, -, -, hq, -⟩
      · exact hℓ (Set.mem_univ ℓ)
      · exact hq (Set.mem_univ q)
  change Algebra.adjoin ℤ (CuspForm.heckeGenerators N k Set.univ) = ⊥
  rw [h, Algebra.adjoin_empty]

open ModularForm in
/-- The primality hypotheses of `ModularForm.coeffHeckeT_comm` are needed: the coefficient
operators `T_4` and `T_2` do not commute. -/
example :
    coeffHeckeT 2 4 (coeffHeckeT 2 2 fun n => if n = 2 then 1 else 0) ≠
      coeffHeckeT 2 2 (coeffHeckeT 2 4 fun n => if n = 2 then 1 else 0) := by
  intro h
  have h1 := congrFun h 1
  norm_num [coeffHeckeT_apply] at h1

/-- The weight hypothesis of `ModularForm.coeffHeckeT_int` is needed: in weight `0`, `T_2` takes
the constant sequence `1` to a sequence whose coefficient at `2` is `3 / 2`. -/
example : ¬ ∃ m : ℤ, ModularForm.coeffHeckeT 0 2 (fun _ => 1) 2 = m := by
  rintro ⟨m, hm⟩
  rw [ModularForm.coeffHeckeT_of_dvd 0 (dvd_refl 2)] at hm
  have h3 : ((3 : ℤ) : ℂ) = ((2 * m : ℤ) : ℂ) := by
    norm_num at hm ⊢
    linear_combination 2 * hm
  have := Int.cast_injective h3
  omega
