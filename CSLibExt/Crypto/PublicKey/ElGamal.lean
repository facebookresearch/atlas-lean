/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Crypto.PublicKey.DiffieHellman
public import Cslib.Probability.PMF

/-!
# ElGamal encryption: correctness, and eavesdropping security from DDH

**ElGamal** (Katz and Lindell, Construction 11.16) over a commutative group `G` with an element
`g` and exponents in `ZMod q`: the secret key is `x`, the public key `h = g ^ x`, and
`encrypt h m y = (g ^ y, h ^ y * m)`, `decrypt x (c₁, c₂) = c₂ / c₁ ^ x`.
`decrypt_encrypt`: decryption inverts encryption for all `x`, `y`, `m`.

**Security**, stated as an exact advantage equality over finite uniform probability spaces, with
no asymptotics. Let `g` generate `G` and `|G| = q`.
* `eavGame q g A : PMF Bool` is the eavesdropping experiment `PubK^eav` for an adversary `A` with
  random coins in a finite type `R`: it chooses two messages from the public key, sees an
  encryption of one of them, and outputs a guess of which; the game outputs whether the guess is
  correct. `eavAdvantage q g A = |Pr[A wins] - 1/2|`.
* `ddhReal q g D` and `ddhRand q g D` are the decisional Diffie–Hellman experiments: the
  distinguisher `D` sees `(g ^ x, g ^ y, g ^ (x y))`, respectively `(g ^ x, g ^ y, g ^ z)`, for
  uniform exponents. `ddhAdvantage q g D = |Pr[D = 1 | real] - Pr[D = 1 | random]|`.
* `reduction A` is the DDH distinguisher that uses its third input as the mask `h ^ y`.
  `eavGame_eq_ddhReal`: with a real DDH triple it runs the eavesdropping game exactly.
  `ddhRand_reduction_true`: with a random triple the mask is a group one-time pad
  (`Cslib.Crypto.Protocols.PerfectSecrecy.groupOTP`, Katz and Lindell, Lemma 11.15), so it
  outputs `true` with probability exactly `1/2`.
* `eavAdvantage_eq_ddhAdvantage`: hence `eavAdvantage q g A = ddhAdvantage q g (reduction A)`,
  and `eavAdvantage_le` turns any DDH advantage bound into an ElGamal one.

This is the eavesdropping part of Katz and Lindell, Theorem 11.18, in exact (non-asymptotic) form.
Its proof then passes from eavesdropping to CPA security for public-key schemes
(Proposition 11.3); that step is not formalized here.

## References

* J. Katz and Y. Lindell, *Introduction to Modern Cryptography*, 2nd ed., CRC Press, 2014,
  Section 11.4.1.
-/

@[expose] public section

namespace Cslib.Crypto.PublicKey.ElGamal

open Finset

/-! ### ElGamal -/

section Scheme

variable {G : Type*} [CommGroup G] {q : ℕ} (g : G)

/-- **ElGamal public key.** Let $G$ be a commutative group with a fixed element $g$ and let $q$ be
a natural number. The public key of a secret key $x \in \mathbb{Z}/q$ is $h = g^{v(x)} \in G$,
where $v(x) \in \{0, \dots, q - 1\}$ is the least nonnegative representative of $x$ if $q \ge 1$,
and $v(x) = |x|$ if $q = 0$ (when $\mathbb{Z}/0 = \mathbb{Z}$). -/
def publicKey (x : ZMod q) : G := gpow g x

/-- **ElGamal encryption.** Let $G$ be a commutative group with a fixed element $g$ and let $q$ be
a natural number. The ElGamal encryption of a message $m \in G$ under the public key $h \in G$
with randomness $y \in \mathbb{Z}/q$ is the pair $(g^y, h^y m) \in G \times G$. Here a power
$k^a$ with $k \in G$ and $a \in \mathbb{Z}/q$ means $k^{v(a)}$, where $v(a) \in \{0, \dots, q - 1\}$
is the least nonnegative representative of $a$ if $q \ge 1$, and $v(a) = |a|$ if $q = 0$ (when
$\mathbb{Z}/0 = \mathbb{Z}$). -/
def encrypt (h m : G) (y : ZMod q) : G × G := (gpow g y, gpow h y * m)

/-- **ElGamal decryption.** Let $G$ be a commutative group and $q$ a natural number. For
$a \in \mathbb{Z}/q\mathbb{Z}$ and $c \in G$ write $c^a$ for $c^{\operatorname{val}(a)}$, where
$\operatorname{val}(a) \in \mathbb{N}$ is the representative of $a$ in $\{0, \dots, q-1\}$ if
$q \ge 1$ and $|a|$ if $q = 0$. Decrypting a ciphertext $(c_1, c_2) \in G \times G$ with the
secret key $x \in \mathbb{Z}/q\mathbb{Z}$ gives $c_2 \cdot (c_1^x)^{-1}$. -/
def decrypt (x : ZMod q) (c : G × G) : G := c.2 * (gpow c.1 x)⁻¹

/-- **Correctness of ElGamal.** Let $G$ be a commutative group, $g \in G$ and $q$ a natural
number. For $a \in \mathbb{Z}/q\mathbb{Z}$ and $c \in G$ write $c^a$ for
$c^{\operatorname{val}(a)}$, where $\operatorname{val}(a) \in \mathbb{N}$ is the representative
of $a$ in $\{0, \dots, q-1\}$ if $q \ge 1$ and $|a|$ if $q = 0$. For every secret key
$x \in \mathbb{Z}/q\mathbb{Z}$, every message $m \in G$ and every encryption randomness
$y \in \mathbb{Z}/q\mathbb{Z}$, decrypting with $x$ the ElGamal encryption of $m$ under the
public key $g^x$ with randomness $y$ returns $m$. -/
theorem decrypt_encrypt (x y : ZMod q) (m : G) :
    decrypt x (encrypt g (publicKey g x) m y) = m := by
  simp only [decrypt, encrypt, publicKey]
  rw [dh_agree g x y, mul_comm (gpow (gpow g x) y) m, mul_inv_cancel_right]

end Scheme

/-! ### Eavesdropping security from DDH -/

section Security

variable {G : Type*} [CommGroup G] [Fintype G] {q : ℕ} [NeZero q] (g : G)
  {R : Type*} [Fintype R] [Nonempty R]

/-- **Message selected by the challenge bit.** Let $G$ be a finite commutative group. For a pair
of messages $(m_0, m_1) \in G \times G$ and a bit $b$, the selected message is $m_1$ if $b$ is
true and $m_0$ if $b$ is false. -/
def pick (m : G × G) (b : Bool) : G := if b then m.2 else m.1

/-- **ElGamal eavesdropping adversary.** Given a type $G$ of public keys and messages and a type
$R$ of random coins, an eavesdropping adversary consists of a choice function, which maps a public
key $h \in G$ and coins $r \in R$ to a pair of messages in $G \times G$, and a guessing function,
which maps a public key $h \in G$, a ciphertext in $G \times G$ and coins $r \in R$ to a bit. -/
structure Adversary (G R : Type*) where
  /-- The two challenge messages, as a function of the public key and the coins. -/
  choose : G → R → G × G
  /-- The guess of the challenge bit. -/
  guess : G → G × G → R → Bool

variable (q) in
/-- **ElGamal eavesdropping experiment.** Let $G$ be a commutative group, $g \in G$ and $q \ge 1$.
For an eavesdropping adversary $A$ with coins in a finite nonempty type $R$, the experiment draws
$x, y \in \mathbb{Z}/q$, coins $r \in R$ and a bit $b$ independently and uniformly. It sets the
public key $h = g^x$, lets $A$ choose messages $(m_0, m_1)$ from $h$ and $r$, and gives $A$ the
key $h$, the ElGamal ciphertext $(g^y, h^y m_b)$ and the coins $r$, where $m_b$ is $m_1$ if $b$
is true and $m_0$ otherwise; powers use the value of the exponent in $\{0, \dots, q - 1\}$. The
experiment outputs the distribution of the bit "the guess of $A$ equals $b$". -/
noncomputable def eavGame (A : Adversary G R) : PMF Bool :=
  (Cslib.Probability.PMF.uniformOfFintype (ZMod q × ZMod q × R × Bool)).map fun ω =>
    A.guess (publicKey g ω.1)
      (encrypt g (publicKey g ω.1) (pick (A.choose (publicKey g ω.1) ω.2.2.1) ω.2.2.2) ω.2.1)
      ω.2.2.1 == ω.2.2.2

variable (q) in
/-- **Eavesdropping advantage against ElGamal.** Let $G$ be a finite commutative group, $g \in G$
and $q \ge 1$. The eavesdropping advantage of an adversary $A$ with random coins in a finite
nonempty type $R$ is the real number $|p - 1/2|$, where $p$ is the probability that $A$ wins the
ElGamal eavesdropping experiment for $g$ with exponents in $\mathbb{Z}/q\mathbb{Z}$, that is,
guesses the challenge bit correctly. -/
noncomputable def eavAdvantage (A : Adversary G R) : ℝ :=
  |(eavGame q g A true).toReal - 1 / 2|

variable {S : Type*} [Fintype S] [Nonempty S]

variable (q) in
/-- **Real DDH experiment.** Let $G$ be a finite commutative group, $g \in G$ and $q \ge 1$ a
natural number, and let $D$ be a distinguisher that maps three elements of $G$ and coins in a
finite nonempty type $S$ to a bit. The real DDH experiment draws $x, y \in \mathbb{Z}/q$ and coins
$s \in S$ independently and uniformly and outputs the distribution of the bit
$D(g^x, g^y, g^{xy}, s)$, where $xy$ is the product in $\mathbb{Z}/q$ and a power $g^a$ with
$a \in \mathbb{Z}/q$ means $g^{v(a)}$ for the representative $v(a) \in \{0, \dots, q - 1\}$
of $a$. -/
noncomputable def ddhReal (D : G → G → G → S → Bool) : PMF Bool :=
  (Cslib.Probability.PMF.uniformOfFintype (ZMod q × ZMod q × S)).map fun ω =>
    D (gpow g ω.1) (gpow g ω.2.1) (gpow g (ω.1 * ω.2.1)) ω.2.2

variable (q) in
/-- **Random DDH experiment.** Let $G$ be a finite commutative group, $g \in G$ and $q \ge 1$ a
natural number, and let $D$ be a distinguisher that maps three elements of $G$ and coins in a
finite nonempty type $S$ to a bit. The random DDH experiment draws $x, y, z \in \mathbb{Z}/q$ and
coins $s \in S$ independently and uniformly and outputs the distribution of the bit
$D(g^x, g^y, g^z, s)$, where a power $g^a$ with $a \in \mathbb{Z}/q$ means $g^{v(a)}$ for the
representative $v(a) \in \{0, \dots, q - 1\}$ of $a$. -/
noncomputable def ddhRand (D : G → G → G → S → Bool) : PMF Bool :=
  (Cslib.Probability.PMF.uniformOfFintype (ZMod q × ZMod q × ZMod q × S)).map fun ω =>
    D (gpow g ω.1) (gpow g ω.2.1) (gpow g ω.2.2.1) ω.2.2.2

variable (q) in
/-- **Advantage of a DDH distinguisher.** Let $G$ be a finite commutative group, $g \in G$ and
$q \ge 1$, and let $D$ be a distinguisher that maps three elements of $G$ and coins in a finite
nonempty type $S$ to a bit. The DDH advantage of $D$ is the real number
$|p_{\mathrm{real}} - p_{\mathrm{rand}}|$, where $p_{\mathrm{real}}$ and $p_{\mathrm{rand}}$ are
the probabilities that $D$ outputs true in the real and in the random DDH experiment for $g$ with
exponents in $\mathbb{Z}/q\mathbb{Z}$. -/
noncomputable def ddhAdvantage (D : G → G → G → S → Bool) : ℝ :=
  |(ddhReal q g D true).toReal - (ddhRand q g D true).toReal|

/-- **DDH distinguisher from an ElGamal eavesdropper.** Let $G$ be a finite commutative group and
let $A$ be an eavesdropping adversary with coins in a finite nonempty type $R$. The distinguisher
built from $A$ takes three elements $X, Y, Z \in G$ and coins consisting of $r \in R$ and a bit
$b$. It lets $A$ choose messages $(m_0, m_1)$ from the public key $X$ and the coins $r$, gives $A$
the public key $X$, the ciphertext $(Y, Z m_b)$ and the coins $r$, where $m_b$ is $m_1$ if $b$ is
true and $m_0$ otherwise, and outputs true exactly when the guess of $A$ equals $b$. -/
def reduction (A : Adversary G R) : G → G → G → R × Bool → Bool :=
  fun X Y Z s => A.guess X (Y, Z * pick (A.choose X s.1) s.2) s.1 == s.2

omit [Fintype G] in
/-- **ElGamal eavesdropping game equals the real DDH experiment of the reduction.** Let $G$ be a
commutative group, $q \ge 1$ a natural number and $g \in G$ with $g^q = 1$. For every
eavesdropping adversary $A$ with coins in a finite nonempty type $R$, the output distribution of
the ElGamal eavesdropping experiment for $A$ (exponents in $\mathbb{Z}/q$) equals the output
distribution of the real DDH experiment run with the distinguisher built from $A$ by the
reduction. -/
theorem eavGame_eq_ddhReal (hg : g ^ q = 1) (A : Adversary G R) :
    eavGame q g A = ddhReal q g (reduction A) := by
  simp only [eavGame, ddhReal, reduction, encrypt, publicKey, gpow_mul hg]

omit [Fintype G] [NeZero q] in
private theorem map_uniform_apply {Ω : Type*} [Fintype Ω] [Nonempty Ω] (f : Ω → Bool)
    (b : Bool) :
    (Cslib.Probability.PMF.uniformOfFintype Ω).map f b =
      (univ.filter fun ω => f ω = b).card * (Fintype.card Ω : ENNReal)⁻¹ := by
  classical
  rw [PMF.map_apply, tsum_fintype]
  simp only [Cslib.Probability.PMF.uniformOfFintype_apply]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
  congr 3
  ext ω
  simp [eq_comm]

omit [Fintype G] [NeZero q] in
/-- If an involution of the sample space flips the outcome, the outcome is a fair coin. -/
private theorem map_uniform_true_eq_half {Ω : Type*} [Fintype Ω] [Nonempty Ω] (f : Ω → Bool)
    (ψ : Ω → Ω) (hψ : Function.Involutive ψ) (hf : ∀ ω, f (ψ ω) = !f ω) :
    (Cslib.Probability.PMF.uniformOfFintype Ω).map f true = 1 / 2 := by
  classical
  rw [map_uniform_apply]
  set c := (univ.filter fun ω => f ω = true).card
  have hc : (univ.filter fun ω => f ω = false).card = c := by
    refine card_nbij' ψ ψ ?_ ?_ (fun ω _ => hψ ω) (fun ω _ => hψ ω) <;>
      · intro ω hω
        simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hω ⊢
        rw [hf, hω]
        rfl
  have hsum : c + c = Fintype.card Ω := by
    rw [← card_univ, ← card_filter_add_card_filter_not (fun ω => f ω = true)]
    congr 1
    simp_rw [Bool.not_eq_true]
    exact hc.symm
  have hc0 : (c : ENNReal) ≠ 0 := by
    have := Fintype.card_pos (α := Ω)
    exact_mod_cast (by omega : c ≠ 0)
  rw [← hsum, Nat.cast_add, ← two_mul, ENNReal.mul_inv (by simp) (by simp), one_div,
    mul_comm (2 : ENNReal)⁻¹, ← mul_assoc, ENNReal.mul_inv_cancel hc0 (by simp), one_mul]

/-- **The reduction is a fair coin on random DDH triples.** Let $G$ be a finite commutative group
of order $q$ generated by $g$. For every eavesdropping adversary $A$ with random coins in a finite
nonempty type $R$, the DDH distinguisher obtained from $A$ by the reduction outputs true with
probability exactly $1/2$ in the random DDH experiment for $g$.

In that experiment the third input $g^z$, with $z$ uniform in $\mathbb{Z}/q\mathbb{Z}$, is a group
one-time pad on the challenge message. -/
theorem ddhRand_reduction_true (hgen : ∀ x : G, x ∈ Subgroup.zpowers g)
    (hcard : Fintype.card G = q) (A : Adversary G R) :
    ddhRand q g (reduction A) true = 1 / 2 := by
  set e := gpowEquiv hgen hcard
  -- flip the bit and shift the mask so that the ciphertext is unchanged
  refine map_uniform_true_eq_half _
    (fun ω => (ω.1, ω.2.1, e.symm (e ω.2.2.1 * pick (A.choose (gpow g ω.1) ω.2.2.2.1) ω.2.2.2.2 *
      (pick (A.choose (gpow g ω.1) ω.2.2.2.1) (!ω.2.2.2.2))⁻¹), ω.2.2.2.1, !ω.2.2.2.2))
    ?_ ?_
  · rintro ⟨x, y, z, r, b⟩
    simp only [Bool.not_not, Equiv.apply_symm_apply, mul_assoc, inv_mul_cancel, mul_one,
      mul_inv_cancel, Equiv.symm_apply_apply]
  · rintro ⟨x, y, z, r, b⟩
    simp only [reduction]
    have h : gpow g (e.symm (e z * pick (A.choose (gpow g x) r) b *
        (pick (A.choose (gpow g x) r) (!b))⁻¹)) * pick (A.choose (gpow g x) r) (!b) =
        gpow g z * pick (A.choose (gpow g x) r) b := by
      rw [← gpowEquiv_apply hgen hcard, Equiv.apply_symm_apply, gpowEquiv_apply,
        inv_mul_cancel_right]
    rw [h]
    cases A.guess (gpow g x) (gpow g y, gpow g z * pick (A.choose (gpow g x) r) b) r <;>
      cases b <;> rfl

/-- **ElGamal eavesdropping advantage equals a DDH advantage.** Let $G$ be a finite commutative
group of order $q$ generated by $g$. For every eavesdropping adversary $A$ with random coins in a
finite nonempty type $R$, the eavesdropping advantage of $A$ against ElGamal equals the DDH
advantage of the distinguisher obtained from $A$ by the reduction.

This is the eavesdropping part of Katz and Lindell, Theorem 11.18 (ElGamal is secure if DDH is
hard), in exact, non-asymptotic form. -/
theorem eavAdvantage_eq_ddhAdvantage (hgen : ∀ x : G, x ∈ Subgroup.zpowers g)
    (hcard : Fintype.card G = q) (A : Adversary G R) :
    eavAdvantage q g A = ddhAdvantage q g (reduction A) := by
  rw [eavAdvantage, ddhAdvantage, eavGame_eq_ddhReal g (hcard ▸ pow_card_eq_one),
    ddhRand_reduction_true g hgen hcard]
  norm_num

/-- **DDH bounds transfer to ElGamal.** Let $G$ be a finite commutative group of order $q$
generated by $g$, and let $A$ be an eavesdropping adversary with random coins in a finite nonempty
type $R$. For every real number $\varepsilon$, if the DDH advantage of the distinguisher obtained
from $A$ by the reduction is at most $\varepsilon$, then the eavesdropping advantage of $A$
against ElGamal is at most $\varepsilon$. -/
theorem eavAdvantage_le (hgen : ∀ x : G, x ∈ Subgroup.zpowers g) (hcard : Fintype.card G = q)
    (A : Adversary G R) {ε : ℝ} (hε : ddhAdvantage q g (reduction A) ≤ ε) :
    eavAdvantage q g A ≤ ε :=
  (eavAdvantage_eq_ddhAdvantage g hgen hcard A).le.trans hε

end Security

end Cslib.Crypto.PublicKey.ElGamal
