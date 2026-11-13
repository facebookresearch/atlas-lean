/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Gauss's theorem on the primitive roots modulo `p^ℓ`

Statements from V. P. Ramesh and S. Sivakumar, "A Note on Gauss's
Theorem on the Primitive Roots Modulo `p^ℓ`", *INTEGERS* 26 (2026),
Article A111 (<https://math.colgate.edu/~integers/aa111/aa111.pdf>,
DOI 10.5281/zenodo.23216790).

Throughout, `p` is an odd prime. The paper's `ord_n(a)`, the order
of `a` in `(ℤ/nℤ)*`, is `mulOrdMod n a` below (defined as `0` when
`a` is not coprime to `n`, a case the paper never uses), and a
*primitive root* of `n` is a generator of `(ℤ/nℤ)*`, here
Mathlib's `IsPrimitiveRoot ((g : ZMod n)) (Nat.totient n)`, i.e.
by `IsPrimitiveRoot.iff_orderOf` a residue of maximal order
`φ(n)`. The paper's fiber `P_a = {x ∈ (ℤ/p²ℤ)* : x ≡ a (mod p)}`
is `liftFiber p a`, defined through the reduction homomorphism
`unitReduceSq p : (ZMod (p^2))ˣ →* (ZMod p)ˣ`.

Lemma 2 of the paper (a finite cyclic group of order `n` has
exactly `φ(ℓ)` elements of order `ℓ` for `ℓ ∣ n`) is already in
Mathlib as `IsCyclic.card_orderOf_eq_totient` and is not restated.
The sentence about Robbins (1975) following Corollary 1 in the
introduction is a narrative citation, not part of any numbered
statement, and is not formalized.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.GaussPrimitiveRootsWanted

/-- The paper's `ord_n(a)`: the multiplicative order of the residue
class of `a` in `(ZMod n)ˣ`, and `0` when `a` is not coprime to
`n`. -/
noncomputable def mulOrdMod (n a : ℕ) : ℕ :=
  if h : Nat.Coprime a n then orderOf (ZMod.unitOfCoprime a h) else 0


/-- Reduction of units modulo `p^2` to units modulo `p`. -/
def unitReduceSq (p : ℕ) : (ZMod (p ^ 2))ˣ →* (ZMod p)ˣ :=
  Units.map (ZMod.castHom (⟨p, by ring⟩ : p ∣ p ^ 2) (ZMod p)).toMonoidHom

/-- The paper's fiber `P_a = {x ∈ (ℤ/p²ℤ)* : x ≡ a (mod p)}`. -/
def liftFiber (p : ℕ) (a : (ZMod (p ^ 2))ˣ) : Set (ZMod (p ^ 2))ˣ :=
  {x | unitReduceSq p x = unitReduceSq p a}

/-- **Lemma 1**: for `a` coprime to the odd prime `p` and any `k`,
`ord_{p²}(a + kp) = ord_p(a)` or `p · ord_p(a)`.

Source: V. P. Ramesh and S. Sivakumar, "A Note on Gauss's Theorem
on the Primitive Roots Modulo `p^ℓ`", Lemma 1. -/
theorem_wanted order_add_mul_prime_eq_or_mul
    (p : ℕ) (hp : p.Prime) (hpo : p ≠ 2) (a k : ℕ)
    (ha : Nat.Coprime a p) :
    mulOrdMod (p ^ 2) (a + k * p) = mulOrdMod p a ∨
      mulOrdMod (p ^ 2) (a + k * p) = p * mulOrdMod p a

/-- **Theorem 2**: for `a` coprime to the odd prime `p`, there
exists a unique `m` modulo `p` such that
`ord_{p²}(a + mp) = ord_p(a)`.

Source: V. P. Ramesh and S. Sivakumar, "A Note on Gauss's Theorem
on the Primitive Roots Modulo `p^ℓ`", Theorem 2. -/
theorem_wanted existsUnique_order_add_mul_prime_eq
    (p : ℕ) (hp : p.Prime) (hpo : p ≠ 2) (a : ℕ)
    (ha : Nat.Coprime a p) :
    ∃! m : ZMod p, mulOrdMod (p ^ 2) (a + m.val * p) = mulOrdMod p a

/-- **Theorem 2**, fiber form: for every `P_a` there exists a
unique `x ∈ P_a` such that `ord_{p²}(x) = ord_p(x)`.

Source: V. P. Ramesh and S. Sivakumar, "A Note on Gauss's Theorem
on the Primitive Roots Modulo `p^ℓ`", Theorem 2. -/
theorem_wanted existsUnique_mem_liftFiber_order_eq
    (p : ℕ) (hp : p.Prime) (hpo : p ≠ 2) (x₀ : (ZMod (p ^ 2))ˣ) :
    ∃! x, x ∈ liftFiber p x₀ ∧ orderOf x = orderOf (unitReduceSq p x)

/-- **Theorem 1** (Gauss): if `g` is a primitive root of the odd
prime `p`, then there exists `k` such that `g + kp` is a primitive
root of `p^ℓ` for all `ℓ ≥ 2`.

Source: V. P. Ramesh and S. Sivakumar, "A Note on Gauss's Theorem
on the Primitive Roots Modulo `p^ℓ`", Theorem 1. -/
theorem_wanted exists_primitiveRoot_add_mul_prime_pow
    (p : ℕ) (hp : p.Prime) (hpo : p ≠ 2) (g : ℕ)
    (hg : IsPrimitiveRoot ((g : ZMod p)) (Nat.totient p)) :
    ∃ k : ℕ, ∀ ℓ : ℕ, 2 ≤ ℓ →
      IsPrimitiveRoot (((g + k * p : ℕ) : ZMod (p ^ ℓ)))
        (Nat.totient (p ^ ℓ))

/-- **Corollary 1**: if `g` is a primitive root of the odd prime
`p`, then there exists a unique `m` modulo `p` such that `g + mp`
is not a primitive root of `p²`, and `g + kp` is a primitive root
of `p²` for every other `k` modulo `p`.

Source: V. P. Ramesh and S. Sivakumar, "A Note on Gauss's Theorem
on the Primitive Roots Modulo `p^ℓ`", Corollary 1. -/
theorem_wanted existsUnique_not_primitiveRoot_add_mul_prime
    (p : ℕ) (hp : p.Prime) (hpo : p ≠ 2) (g : ℕ)
    (hg : IsPrimitiveRoot ((g : ZMod p)) (Nat.totient p)) :
    ∃! m : ZMod p,
      ¬ IsPrimitiveRoot (((g + m.val * p : ℕ) : ZMod (p ^ 2)))
          (Nat.totient (p ^ 2)) ∧
        ∀ k : ZMod p, k ≠ m →
          IsPrimitiveRoot (((g + k.val * p : ℕ) : ZMod (p ^ 2)))
            (Nat.totient (p ^ 2))

/-- **Corollary 1**, fiber form: if `g` is a primitive root of the
odd prime `p`, then there exists a unique `x ∈ P_g` such that
`ord_{p²}(x) = p - 1`.

Source: V. P. Ramesh and S. Sivakumar, "A Note on Gauss's Theorem
on the Primitive Roots Modulo `p^ℓ`", Corollary 1. -/
theorem_wanted existsUnique_mem_liftFiber_order_eq_sub_one
    (p : ℕ) (hp : p.Prime) (hpo : p ≠ 2) (g : ℕ)
    (hg : IsPrimitiveRoot ((g : ZMod p)) (Nat.totient p)) :
    ∃! x, x ∈ liftFiber p (ZMod.unitOfCoprime g
        (((ZMod.isUnit_iff_coprime g p).mp
          (hg.isUnit (Nat.totient_pos.mpr hp.pos).ne')).pow_right 2)) ∧
      orderOf x = p - 1

/-- **Theorem 3**: if `g` is a primitive root of the odd prime `p`
and `k ≢ 0 (mod p)`, then `g^p + kp` is a primitive root of `p^ℓ`
for all `ℓ > 1`.

Source: V. P. Ramesh and S. Sivakumar, "A Note on Gauss's Theorem
on the Primitive Roots Modulo `p^ℓ`", Theorem 3. -/
theorem_wanted primitiveRoot_pow_add_mul_prime_pow
    (p : ℕ) (hp : p.Prime) (hpo : p ≠ 2) (g k : ℕ)
    (hg : IsPrimitiveRoot ((g : ZMod p)) (Nat.totient p))
    (hk : ¬ p ∣ k) :
    ∀ ℓ : ℕ, 1 < ℓ →
      IsPrimitiveRoot (((g ^ p + k * p : ℕ) : ZMod (p ^ ℓ)))
        (Nat.totient (p ^ ℓ))

/-- **Lemma 3**: for any endomorphism `f` of `(ZMod (p^2))ˣ` and
any `a`, `f '' P_a ⊆ P_{f a}`.

Source: V. P. Ramesh and S. Sivakumar, "A Note on Gauss's Theorem
on the Primitive Roots Modulo `p^ℓ`", Lemma 3. -/
theorem_wanted monoidHom_image_liftFiber_subset
    (p : ℕ) (hp : p.Prime) (hpo : p ≠ 2)
    (f : (ZMod (p ^ 2))ˣ →* (ZMod (p ^ 2))ˣ) (a : (ZMod (p ^ 2))ˣ) :
    f '' liftFiber p a ⊆ liftFiber p (f a)

/-- **Lemma 4**: for `n` coprime to both the odd prime `p` and
`ord_{p²}(a)`, the power map `x ↦ x^n` is injective on `P_a`,
maps `P_a` onto `P_{a^n}`, and preserves the order of every
element of `P_a`.

Source: V. P. Ramesh and S. Sivakumar, "A Note on Gauss's Theorem
on the Primitive Roots Modulo `p^ℓ`", Lemma 4. -/
theorem_wanted pow_injectiveOn_liftFiber_and_order_eq
    (p : ℕ) (hp : p.Prime) (hpo : p ≠ 2) (a : (ZMod (p ^ 2))ˣ)
    (n : ℕ) (hnp : Nat.Coprime n p) (hno : Nat.Coprime n (orderOf a)) :
    Set.InjOn (fun x => x ^ n) (liftFiber p a) ∧
      (fun x => x ^ n) '' liftFiber p a = liftFiber p (a ^ n) ∧
      ∀ b ∈ liftFiber p a, orderOf (b ^ n) = orderOf b

end MathlibExt.NumberTheory.GaussPrimitiveRootsWanted
