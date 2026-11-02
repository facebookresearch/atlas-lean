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

/-- **Multiplicative order modulo $n$.** For natural numbers $n$ and $a$,
$\operatorname{ord}_n(a)$ is the multiplicative order of the residue class of $a$ in the
unit group $(\mathbb{Z}/n\mathbb{Z})^\times$ when $a$ is coprime to $n$, and $0$
otherwise. -/
noncomputable def mulOrdMod (n a : ℕ) : ℕ :=
  if h : Nat.Coprime a n then orderOf (ZMod.unitOfCoprime a h) else 0


/-- **Reduction of units modulo $p^2$ to units modulo $p$.** For a natural number $p$, this is
the group homomorphism $(\mathbb{Z}/p^2\mathbb{Z})^\times \to (\mathbb{Z}/p\mathbb{Z})^\times$
induced on units by the reduction ring homomorphism
$\mathbb{Z}/p^2\mathbb{Z} \to \mathbb{Z}/p\mathbb{Z}$, which sends the class of $x$ modulo $p^2$ to
the class of $x$ modulo $p$. -/
def unitReduceSq (p : ℕ) : (ZMod (p ^ 2))ˣ →* (ZMod p)ˣ :=
  Units.map (ZMod.castHom (⟨p, by ring⟩ : p ∣ p ^ 2) (ZMod p)).toMonoidHom

/-- **Fibers of reduction modulo $p$ on units modulo $p^2$.** For a natural number $p$ and a unit
$a$ of $\mathbb{Z}/p^2\mathbb{Z}$, the fiber $P_a$ is the set of units $x$ of
$\mathbb{Z}/p^2\mathbb{Z}$ with $x \equiv a \pmod p$, that is, the units whose image under the
reduction map $(\mathbb{Z}/p^2\mathbb{Z})^\times \to (\mathbb{Z}/p\mathbb{Z})^\times$ equals the
image of $a$. -/
def liftFiber (p : ℕ) (a : (ZMod (p ^ 2))ˣ) : Set (ZMod (p ^ 2))ˣ :=
  {x | unitReduceSq p x = unitReduceSq p a}

/-- **The order of $a + kp$ modulo $p^2$.** Let $p$ be an odd prime and let $a$ and $k$ be
natural numbers with $a$ coprime to $p$. Writing $\operatorname{ord}_n(b)$ for the
multiplicative order of $b$ modulo $n$, the order $\operatorname{ord}_{p^2}(a + kp)$ is
either $\operatorname{ord}_p(a)$ or $p \cdot \operatorname{ord}_p(a)$.

Source: V. P. Ramesh and S. Sivakumar, "A Note on Gauss's Theorem
on the Primitive Roots Modulo `p^ℓ`", Lemma 1. -/
theorem_wanted order_add_mul_prime_eq_or_mul
    (p : ℕ) (hp : p.Prime) (hpo : p ≠ 2) (a k : ℕ)
    (ha : Nat.Coprime a p) :
    mulOrdMod (p ^ 2) (a + k * p) = mulOrdMod p a ∨
      mulOrdMod (p ^ 2) (a + k * p) = p * mulOrdMod p a

/-- **Unique order-preserving lift modulo $p^2$.** Let $p$ be an odd prime and let $a$ be
a natural number coprime to $p$. Writing $\operatorname{ord}_n(b)$ for the multiplicative
order of $b$ modulo $n$, there is exactly one $m \in \{0, 1, \dots, p - 1\}$ such that
$\operatorname{ord}_{p^2}(a + mp) = \operatorname{ord}_p(a)$.

Source: V. P. Ramesh and S. Sivakumar, "A Note on Gauss's Theorem
on the Primitive Roots Modulo `p^ℓ`", Theorem 2. -/
theorem_wanted existsUnique_order_add_mul_prime_eq
    (p : ℕ) (hp : p.Prime) (hpo : p ≠ 2) (a : ℕ)
    (ha : Nat.Coprime a p) :
    ∃! m : ZMod p, mulOrdMod (p ^ 2) (a + m.val * p) = mulOrdMod p a

/-- **Unique order-preserving element of a fiber modulo $p^2$.** Let $p$ be an odd prime,
let $x_0$ be a unit modulo $p^2$, and let $P_{x_0}$ be the set of units $x$ modulo $p^2$
with $x \equiv x_0 \pmod p$. There is exactly one $x \in P_{x_0}$ whose multiplicative
order modulo $p^2$ equals the multiplicative order of its reduction modulo $p$.

Source: V. P. Ramesh and S. Sivakumar, "A Note on Gauss's Theorem
on the Primitive Roots Modulo `p^ℓ`", Theorem 2. -/
theorem_wanted existsUnique_mem_liftFiber_order_eq
    (p : ℕ) (hp : p.Prime) (hpo : p ≠ 2) (x₀ : (ZMod (p ^ 2))ˣ) :
    ∃! x, x ∈ liftFiber p x₀ ∧ orderOf x = orderOf (unitReduceSq p x)

/-- **Gauss's theorem on primitive roots modulo prime powers.** Let $p$ be an odd prime
and let $g$ be a natural number that is a primitive root modulo $p$, where a primitive
root modulo $n$ is a residue class modulo $n$ of multiplicative order $\varphi(n)$. Then
there is a natural number $k$ such that $g + kp$ is a primitive root modulo $p^\ell$ for
every $\ell \ge 2$.

Source: V. P. Ramesh and S. Sivakumar, "A Note on Gauss's Theorem
on the Primitive Roots Modulo `p^ℓ`", Theorem 1. -/
theorem_wanted exists_primitiveRoot_add_mul_prime_pow
    (p : ℕ) (hp : p.Prime) (hpo : p ≠ 2) (g : ℕ)
    (hg : IsPrimitiveRoot ((g : ZMod p)) (Nat.totient p)) :
    ∃ k : ℕ, ∀ ℓ : ℕ, 2 ≤ ℓ →
      IsPrimitiveRoot (((g + k * p : ℕ) : ZMod (p ^ ℓ)))
        (Nat.totient (p ^ ℓ))

/-- **Exactly one lift of a primitive root fails modulo $p^2$.** Let $p$ be an odd prime
and let $g$ be a natural number that is a primitive root modulo $p$, where a primitive
root modulo $n$ is a residue class modulo $n$ of multiplicative order $\varphi(n)$. Then
there is exactly one $m \in \{0, 1, \dots, p - 1\}$ such that $g + mp$ is not a primitive
root modulo $p^2$, and $g + kp$ is a primitive root modulo $p^2$ for every other
$k \in \{0, 1, \dots, p - 1\}$.

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

/-- **The lift of order $p - 1$ of a primitive root.** Let $p$ be an odd prime and let
$g$ be a natural number that is a primitive root modulo $p$, that is, a residue class
modulo $p$ of multiplicative order $\varphi(p) = p - 1$. Let $P_g$ be the set of units
$x$ modulo $p^2$ with $x \equiv g \pmod p$. Then exactly one $x \in P_g$ has
multiplicative order $p - 1$ modulo $p^2$.

Source: V. P. Ramesh and S. Sivakumar, "A Note on Gauss's Theorem
on the Primitive Roots Modulo `p^ℓ`", Corollary 1. -/
theorem_wanted existsUnique_mem_liftFiber_order_eq_sub_one
    (p : ℕ) (hp : p.Prime) (hpo : p ≠ 2) (g : ℕ)
    (hg : IsPrimitiveRoot ((g : ZMod p)) (Nat.totient p)) :
    ∃! x, x ∈ liftFiber p (ZMod.unitOfCoprime g
        (((ZMod.isUnit_iff_coprime g p).mp
          (hg.isUnit (Nat.totient_pos.mpr hp.pos).ne')).pow_right 2)) ∧
      orderOf x = p - 1

/-- **Primitive roots modulo $p^\ell$ of the form $g^p + kp$.** Let $p$ be an odd prime and let
$g$ be a natural number that is a primitive root modulo $p$. If $k$ is a natural number not
divisible by $p$, then $g^p + kp$ is a primitive root modulo $p^\ell$ for every natural number
$\ell > 1$.

Here a natural number $a$ is a primitive root modulo $n$ when its residue class in
$\mathbb{Z}/n\mathbb{Z}$ is a primitive $\varphi(n)$-th root of unity, where $\varphi$ is Euler's
totient function.

Source: V. P. Ramesh and S. Sivakumar, "A Note on Gauss's Theorem
on the Primitive Roots Modulo `p^ℓ`", Theorem 3. -/
theorem_wanted primitiveRoot_pow_add_mul_prime_pow
    (p : ℕ) (hp : p.Prime) (hpo : p ≠ 2) (g k : ℕ)
    (hg : IsPrimitiveRoot ((g : ZMod p)) (Nat.totient p))
    (hk : ¬ p ∣ k) :
    ∀ ℓ : ℕ, 1 < ℓ →
      IsPrimitiveRoot (((g ^ p + k * p : ℕ) : ZMod (p ^ ℓ)))
        (Nat.totient (p ^ ℓ))

/-- **Endomorphisms of the units modulo $p^2$ respect the fibers.** Let $p$ be an odd
prime, let $f$ be a group endomorphism of $(\mathbb{Z}/p^2\mathbb{Z})^\times$, and let
$a$ be a unit modulo $p^2$. Writing $P_b$ for the set of units $x$ modulo $p^2$ with
$x \equiv b \pmod p$, the image of $P_a$ under $f$ is contained in $P_{f(a)}$.

Source: V. P. Ramesh and S. Sivakumar, "A Note on Gauss's Theorem
on the Primitive Roots Modulo `p^ℓ`", Lemma 3. -/
theorem_wanted monoidHom_image_liftFiber_subset
    (p : ℕ) (hp : p.Prime) (hpo : p ≠ 2)
    (f : (ZMod (p ^ 2))ˣ →* (ZMod (p ^ 2))ˣ) (a : (ZMod (p ^ 2))ˣ) :
    f '' liftFiber p a ⊆ liftFiber p (f a)

/-- **Power maps on the fibers modulo $p^2$.** Let $p$ be an odd prime, let $a$ be a unit
modulo $p^2$, and let $n$ be a natural number coprime to $p$ and to the multiplicative
order of $a$. Writing $P_b$ for the set of units $x$ modulo $p^2$ with
$x \equiv b \pmod p$, the map $x \mapsto x^n$ is injective on $P_a$, maps $P_a$ onto
$P_{a^n}$, and preserves the multiplicative order of every element of $P_a$.

Source: V. P. Ramesh and S. Sivakumar, "A Note on Gauss's Theorem
on the Primitive Roots Modulo `p^ℓ`", Lemma 4. -/
theorem_wanted pow_injectiveOn_liftFiber_and_order_eq
    (p : ℕ) (hp : p.Prime) (hpo : p ≠ 2) (a : (ZMod (p ^ 2))ˣ)
    (n : ℕ) (hnp : Nat.Coprime n p) (hno : Nat.Coprime n (orderOf a)) :
    Set.InjOn (fun x => x ^ n) (liftFiber p a) ∧
      (fun x => x ^ n) '' liftFiber p a = liftFiber p (a ^ n) ∧
      ∀ b ∈ liftFiber p a, orderOf (b ^ n) = orderOf b

end MathlibExt.NumberTheory.GaussPrimitiveRootsWanted
