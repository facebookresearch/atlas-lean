/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Crypto.PublicKey.DiffieHellman
public import Cslib.Probability.PMF
public import Mathlib.Algebra.Field.ZMod

/-!
# The Schnorr identification scheme: completeness, special soundness, zero knowledge

In a commutative group `G` with an element `g` of order dividing `q`, the prover knows `x` with
`y = g ^ x` (exponents in `ZMod q`, `gpow`). One run of the protocol:
the prover sends `I = g ^ k` for a uniform `k`, the verifier sends a uniform challenge `r`, the
prover answers `s = r x + k`, and the verifier accepts when `g ^ s * (y ^ r)⁻¹ = I`.

* `accepts_honest` (**completeness**): honest transcripts are always accepted.
* `extract_spec` (**special soundness**): for `q` prime, from two accepting transcripts
  `(I, r, s)` and `(I, r', s')` with the same commitment and `r ≠ r'`, the extractor
  `(s - s') / (r - r')` is a discrete logarithm of `y`, whenever `g ^ q = 1` and `y ^ q = 1`: the
  two transcripts determine a discrete logarithm of `y`.
* `transcript_eq_simulate` (**honest-verifier zero knowledge**, perfect): the distribution of honest
  transcripts equals that of the simulator, which samples `r` and `s` uniformly and sets
  `I = g ^ s * (y ^ r)⁻¹` without knowing `x`.

## References

* J. Katz and Y. Lindell, *Introduction to Modern Cryptography*, 2nd ed., CRC Press, 2014,
  Section 12.5 (the Schnorr identification scheme, Figure 12.2). Completeness is the scheme's
  correctness; transcript simulation and extraction from two accepting transcripts are the
  ingredients of the security proof of Theorem 12.11.
-/

@[expose] public section

namespace Cslib.Crypto.Identification.Schnorr

open Cslib.Crypto.PublicKey

variable {G : Type*} [CommGroup G] {q : ℕ} (g y : G)

/-- **Schnorr verifier's acceptance condition.** Let $G$ be a commutative group, $q$ a natural
number and $g, y \in G$ (the base and the public key); for $h \in G$ and $a \in \mathbb{Z}/q$
write $h^a$ for $h^{\bar a}$, where $\bar a$ is the representative of $a$ in
$\{0, \dots, q - 1\}$ (and $\bar a = |a|$ when $q = 0$, so that $\mathbb{Z}/q = \mathbb{Z}$).
The verifier accepts a transcript $(I, r, s)$ with $I \in G$ and $r, s \in \mathbb{Z}/q$ when
$g^s (y^r)^{-1} = I$. -/
def Accepts (I : G) (r s : ZMod q) : Prop := gpow g s * (gpow y r)⁻¹ = I

/-- **Schnorr prover's response.** Let $q$ be a natural number. For a secret key $x$, prover
randomness $k$ and challenge $r$, all in $\mathbb{Z}/q$, the prover's answer is
$s = rx + k \in \mathbb{Z}/q$. -/
def respond (x k r : ZMod q) : ZMod q := r * x + k

private theorem gpow_sub [NeZero q] {g : G} (hg : g ^ q = 1) (a b : ZMod q) :
    gpow g (a - b) = gpow g a * (gpow g b)⁻¹ := by
  rw [eq_mul_inv_iff_mul_eq, ← gpow_add hg, sub_add_cancel]

/-- **Completeness of the Schnorr identification scheme.** Let $G$ be a commutative group,
$q \ge 1$ a natural number and $g \in G$ with $g^q = 1$; for $h \in G$ and $a \in \mathbb{Z}/q$
write $h^a$ for $h^{\bar a}$, where $\bar a \in \{0, \dots, q - 1\}$ is the representative
of $a$. For all $x, k, r \in \mathbb{Z}/q$, with public key $y = g^x$, the honest transcript
$(g^k, r, rx + k)$ is accepted, that is, $g^{rx + k} (y^r)^{-1} = g^k$. -/
theorem accepts_honest [NeZero q] {g : G} (hg : g ^ q = 1) (x k r : ZMod q) :
    Accepts g (gpow g x) (gpow g k) r (respond x k r) := by
  rw [Accepts, respond, gpow_add hg, mul_comm r x, gpow_mul hg, mul_comm, ← mul_assoc,
    inv_mul_cancel, one_mul]

/-- **Schnorr knowledge extractor.** Let $q$ be a natural number. For
$r, s, r', s' \in \mathbb{Z}/q$ (the challenges and answers of two transcripts), the extracted
exponent is $(s - s')(r - r')^{-1} \in \mathbb{Z}/q$, where $u^{-1}$ is the inverse of $u$ in
$\mathbb{Z}/q$ when $u$ is a unit (and, otherwise, a conventional element of $\mathbb{Z}/q$
depending on $u$). For $q$ prime and $r \ne r'$ it is $(s - s')/(r - r')$. -/
def extract (r s r' s' : ZMod q) : ZMod q := (s - s') * (r - r')⁻¹

/-- **Special soundness.** Let $G$ be a commutative group, $q$ a prime and $g, y \in G$ with
$g^q = 1$ and $y^q = 1$; for $h \in G$ and $a \in \mathbb{Z}/q$ write $h^a$ for $h^{\bar a}$,
where $\bar a \in \{0, \dots, q - 1\}$ is the representative of $a$. Let $I \in G$ and
$r, s, r', s' \in \mathbb{Z}/q$ with $r \ne r'$, and suppose both transcripts $(I, r, s)$ and
$(I, r', s')$ are accepted, that is, $g^s (y^r)^{-1} = I$ and $g^{s'} (y^{r'})^{-1} = I$. Then
the extracted exponent $e = (s - s')(r - r')^{-1}$ is a discrete logarithm of $y$: $g^e = y$. -/
theorem extract_spec [Fact q.Prime] {g y : G} (hg : g ^ q = 1) (hy : y ^ q = 1) {I : G}
    {r s r' s' : ZMod q} (hrr : r ≠ r') (h₁ : Accepts g y I r s) (h₂ : Accepts g y I r' s') :
    gpow g (extract r s r' s') = y := by
  have hsub : gpow g (s - s') = gpow y (r - r') := by
    rw [gpow_sub hg, gpow_sub hy]
    rw [Accepts, mul_inv_eq_iff_eq_mul] at h₁ h₂
    rw [h₁, h₂, ← div_eq_mul_inv, ← div_eq_mul_inv, mul_div_mul_left_eq_div]
  have hunit : IsUnit (r - r') := isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr hrr)
  have hone : gpow y (1 : ZMod q) = y := by
    rw [gpow, ZMod.val_one, pow_one]
  rw [extract, gpow_mul hg, hsub, ← gpow_mul hy,
    ZMod.mul_inv_of_unit _ hunit, hone]

/-! ### Honest-verifier zero knowledge -/

section ZeroKnowledge

variable [NeZero q]

/-- **Honest Schnorr transcript.** Let $G$ be a commutative group, $q \ge 1$ and $g \in G$; for
$a \in \mathbb{Z}/q$ write $g^a$ for $g^{\bar a}$, where $\bar a \in \{0, \dots, q - 1\}$ is the
representative of $a$. For a secret key $x$, prover randomness $k$ and challenge $r$, all in
$\mathbb{Z}/q$, the honest transcript is the element $(g^k, r, rx + k)$ of
$G \times \mathbb{Z}/q \times \mathbb{Z}/q$. -/
def honestTranscript (x : ZMod q) (kr : ZMod q × ZMod q) : G × ZMod q × ZMod q :=
  (gpow g kr.1, kr.2, respond x kr.1 kr.2)

/-- **Simulated Schnorr transcript.** Let $G$ be a commutative group, $q \ge 1$ and $g, y \in G$;
for $h \in G$ and $a \in \mathbb{Z}/q$ write $h^a$ for $h^{\bar a}$, where
$\bar a \in \{0, \dots, q - 1\}$ is the representative of $a$. For a challenge $r$ and an answer
$s$ in $\mathbb{Z}/q$, the simulated transcript is the element $(g^s (y^r)^{-1}, r, s)$ of
$G \times \mathbb{Z}/q \times \mathbb{Z}/q$. -/
def simTranscript (rs : ZMod q × ZMod q) : G × ZMod q × ZMod q :=
  (gpow g rs.2 * (gpow y rs.1)⁻¹, rs.1, rs.2)

/-- **Distribution of honest Schnorr transcripts.** Let $G$ be a commutative group, $q \ge 1$ and
$g \in G$; for $a \in \mathbb{Z}/q$ write $g^a$ for $g^{\bar a}$, where
$\bar a \in \{0, \dots, q - 1\}$ is the representative of $a$. For a secret key
$x \in \mathbb{Z}/q$, this is the law of the honest transcript $(g^k, r, rx + k)$ when $(k, r)$ is
uniform on $\mathbb{Z}/q \times \mathbb{Z}/q$. -/
noncomputable def transcript (x : ZMod q) : PMF (G × ZMod q × ZMod q) :=
  (Cslib.Probability.PMF.uniformOfFintype (ZMod q × ZMod q)).map (honestTranscript g x)

/-- **Schnorr simulator.** Let $G$ be a commutative group, $q \ge 1$ and $g, y \in G$; for
$h \in G$ and $a \in \mathbb{Z}/q$ write $h^a$ for $h^{\bar a}$, where
$\bar a \in \{0, \dots, q - 1\}$ is the representative of $a$. The simulator's distribution is
the law of the simulated transcript $(g^s (y^r)^{-1}, r, s)$ when $(r, s)$ is uniform on
$\mathbb{Z}/q \times \mathbb{Z}/q$; it uses only $g$ and the public key $y$. -/
noncomputable def simulate : PMF (G × ZMod q × ZMod q) :=
  (Cslib.Probability.PMF.uniformOfFintype (ZMod q × ZMod q)).map (simTranscript g y)

/-- **Perfect honest-verifier zero knowledge.** Let $G$ be a commutative group, $q \ge 1$ and
$g \in G$ with $g^q = 1$; for $h \in G$ and $a \in \mathbb{Z}/q$ write $h^a$ for $h^{\bar a}$,
where $\bar a \in \{0, \dots, q - 1\}$ is the representative of $a$. For every secret key
$x \in \mathbb{Z}/q$, with public key $y = g^x$, the honest transcript $(g^k, r, rx + k)$ with
$(k, r)$ uniform on $\mathbb{Z}/q \times \mathbb{Z}/q$ has the same distribution as the
simulated transcript $(g^s (y^r)^{-1}, r, s)$ with $(r, s)$ uniform on
$\mathbb{Z}/q \times \mathbb{Z}/q$. -/
theorem transcript_eq_simulate {g : G} (hg : g ^ q = 1) (x : ZMod q) :
    transcript g x = simulate g (gpow g x) := by
  let e : ZMod q × ZMod q ≃ ZMod q × ZMod q :=
    { toFun := fun kr => (kr.2, respond x kr.1 kr.2)
      invFun := fun rs => (rs.2 - rs.1 * x, rs.1)
      left_inv := fun kr => by simp [respond]
      right_inv := fun rs => by simp [respond] }
  have hcomp : honestTranscript g x = simTranscript g (gpow g x) ∘ e := by
    funext kr
    simp only [honestTranscript, simTranscript, Function.comp, e, Equiv.coe_fn_mk, respond]
    congr 1
    rw [gpow_add hg, mul_comm kr.2 x, gpow_mul hg, mul_comm, ← mul_assoc, inv_mul_cancel,
      one_mul]
  rw [transcript, simulate, hcomp, ← PMF.map_comp, Cslib.Probability.PMF.uniformOfFintype_map_equiv]

end ZeroKnowledge

end Cslib.Crypto.Identification.Schnorr
