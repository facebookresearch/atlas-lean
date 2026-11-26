/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Crypto.Framework.Asymptotic
public import Mathlib.Data.Set.Finite.Basic

/-!
# Key-indexed trapdoor function and permutation schemes

A possible output of key generation selects two finite sets of bitstrings. Evaluation sees the
public key, inversion sees the matching secret key. A left inverse need not be a right inverse
unless the two spaces coincide. Neither inverse law asserts computational one-wayness.

Boneh and Shoup, *A Graduate Course in Applied Cryptography*, v0.4 (2017), §§10.2–10.3:
Definition 10.4 indexes the spaces by a security parameter and a **system** parameter generated
before the keys. Allowing them also to depend on the public key is the extension discussed on
p. 399. This file uses a strict bounded-coin model: the challenge is exactly uniform, and an
exact polynomial-time sampler is a condition on a scheme, not a consequence of finiteness.
Definitions 2.8–2.9 also allow exact samplers with a negligible probability of exceeding their
polynomial time bound. The two sampling conventions are not identical. The adversaries below
also use strict polynomial time; no identification of machine models is needed.
-/

@[expose] public section

namespace Cslib.Crypto.PublicKey.Trapdoor

open MetaMathlibExt.ComplexityTheory Cslib.Crypto.Framework
open Cslib.Probability.PMF (uniformOfFinset uniformOfFintype)

local notation "Bits" => List Bool
local notation "Index" => Bits × Bits × Bits

/-- The bitstring inputs common to a deterministic map: the positive security parameter in
unary, the public system parameter, and the relevant key (public or secret). -/
abbrev index (n : ℕ+) (pp k : Bits) : Index := (List.replicate n.val true, pp, k)

/-- **Data of a key-indexed trapdoor family.** At a positive security parameter the setup law
selects a public system parameter, then the key law selects a matching public and secret key.
The domain and codomain are finite sets of bitstrings indexed by the public context. Evaluation
and inversion are deterministic bitstring functions; the last key in their respective contexts
is the public key and the secret key. No efficiency, correctness or security is implicit. -/
structure Family where
  setup : ℕ+ → PMF Bits
  keys : ℕ+ → Bits → PMF (Bits × Bits)
  domain : Index → Finset Bits
  codomain : Index → Finset Bits
  eval : Index × Bits → Bits
  invert : Index × Bits → Bits

namespace Family

variable (S : Family)

/-- A public system parameter and a key pair are legal if setup can select that parameter and
key generation at that parameter can output that very pair. Neither law has to be uniform. -/
def Generated (n : ℕ+) (pp pk sk : Bits) : Prop :=
  pp ∈ (S.setup n).support ∧ (pk, sk) ∈ (S.keys n pp).support

/-- **Trapdoor correctness at matching keys.** The public map takes the finite domain to the
codomain; the secret map takes the entire codomain to the domain and is a left inverse there
on public images. On points of the codomain outside the image its value need not be special. -/
def CorrectAt (n : ℕ+) (pp pk sk : Bits) : Prop :=
  let pub := index n pp pk
  let sec := index n pp sk
  let f := fun x => S.eval (pub, x)
  let i := fun y => S.invert (sec, y)
  Set.MapsTo f (S.domain pub) (S.codomain pub) ∧
    Set.MapsTo i (S.codomain pub) (S.domain pub) ∧ Set.LeftInvOn i f (S.domain pub)

/-- **Finite-domain inverse laws.** At keys satisfying trapdoor correctness, if the codomain
is the domain, the public map is bijective on that set and the matching secret map is also a
right inverse on it. This uses finiteness for surjectivity, not a hardness hypothesis. -/
theorem CorrectAt.bijOn_and_rightInvOn {S : Family} {n : ℕ+} {pp pk sk : Bits}
    (h : S.CorrectAt n pp pk sk) (heq : S.codomain (index n pp pk) = S.domain (index n pp pk)) :
    let pub := index n pp pk
    let f := fun x => S.eval (pub, x)
    Set.BijOn f (S.domain pub) (S.domain pub) ∧
      Set.RightInvOn (fun y => S.invert (index n pp sk, y)) f (S.domain pub) := by
  obtain ⟨hf, _, hi⟩ := h
  rw [heq] at hf
  have hb := ((S.domain _).finite_toSet.injOn_iff_bijOn_of_mapsTo hf).mp hi.injOn
  exact ⟨hb, hb.surjOn.leftInvOn_of_rightInvOn hi⟩

local notation "coins" => (fun m : ℕ => _root_.PMF.map List.ofFn (uniformOfFintype (Fin m → Bool)))

/-- **Efficient key-indexed trapdoor function scheme, exact bounded-coin convention.** There
are uniform polynomial-time algorithms for setup, key generation and sampling, each applied
to a fresh uniform bitstring whose length is a fixed polynomial in the positive security
parameter. They realise the specified setup and conditional key laws and the exact uniform
law of the nonempty domain at every generated public context. Both spaces have uniform
polynomial-time membership tests at those contexts; enumeration is not required. The public
and secret maps are polynomial-time. One polynomial bounds the lengths of every generated
system parameter, both keys and all words in either space. Correctness holds at every generated
pair. The spaces may also depend on the public key, not just on the system parameter. -/
structure IsFunctionScheme : Prop where
  setup_law : ∃ (q : Polynomial ℕ) (P : Bits × Bits → Bits), IsPolyTime P ∧ ∀ n : ℕ+,
    (coins (q.eval n.val)).map (fun r => P (List.replicate n.val true, r)) = S.setup n
  key_law : ∃ (q : Polynomial ℕ) (G : Index → Bits × Bits), IsPolyTime G ∧
    ∀ (n : ℕ+) (pp), pp ∈ (S.setup n).support →
      (coins (q.eval n.val)).map (fun r => G (index n pp r)) = S.keys n pp
  sample_law : ∃ (q : Polynomial ℕ) (sample : Index × Bits → Bits), IsPolyTime sample ∧
    ∀ (n : ℕ+) (pp pk sk), S.Generated n pp pk sk →
      let pub := index n pp pk
      ∃ hx : (S.domain pub).Nonempty,
        (coins (q.eval n.val)).map (fun r => sample (pub, r)) = uniformOfFinset (S.domain pub) hx
  recognize : ∃ (X Y : Index × Bits → Bool), IsPolyTime X ∧ IsPolyTime Y ∧
    ∀ (n : ℕ+) (pp pk sk), S.Generated n pp pk sk → ∀ z : Bits,
      let pub := index n pp pk
      (X (pub, z) = true ↔ z ∈ S.domain pub) ∧ (Y (pub, z) = true ↔ z ∈ S.codomain pub)
  eval_polyTime : IsPolyTime S.eval
  invert_polyTime : IsPolyTime S.invert
  length_bound : ∃ p : Polynomial ℕ, ∀ (n : ℕ+) (pp pk sk), S.Generated n pp pk sk →
    pp.length ≤ p.eval n.val ∧ pk.length ≤ p.eval n.val ∧ sk.length ≤ p.eval n.val ∧
    ∀ z ∈ S.domain (index n pp pk) ∪ S.codomain (index n pp pk), z.length ≤ p.eval n.val
  correct : ∀ (n : ℕ+) (pp pk sk), S.Generated n pp pk sk → S.CorrectAt n pp pk sk

/-- Exact uniform sampling requires a nonempty domain at each generated public context. -/
theorem IsFunctionScheme.domain_nonempty {S : Family} (h : S.IsFunctionScheme)
    (n : ℕ+) (pp pk sk : Bits) (hg : S.Generated n pp pk sk) :
    (S.domain (index n pp pk)).Nonempty := by
  obtain ⟨_, _, _, hs⟩ := h.sample_law
  exact (hs n pp pk sk hg).choose

/-- **A restriction of exact bounded-coin sampling.** In a trapdoor function scheme there is
one polynomial $q$ such that the cardinality of every generated domain divides $2^{q(n)}$
at security parameter $n$. Each domain point must have the same number of sampling tapes. -/
theorem IsFunctionScheme.card_domain_dvd {S : Family} (h : S.IsFunctionScheme) :
    ∃ q : Polynomial ℕ, ∀ (n : ℕ+) (pp pk sk), S.Generated n pp pk sk →
      (S.domain (index n pp pk)).card ∣ 2 ^ q.eval n.val := by
  classical
  obtain ⟨q, sample, _, hs⟩ := h.sample_law
  refine ⟨q, fun n pp pk sk hg => ?_⟩
  obtain ⟨hne, hlaw⟩ := hs n pp pk sk hg
  let s := S.domain (index n pp pk)
  have hne' : s.Nonempty := hne
  obtain ⟨x, hx⟩ := hne
  have hx' : x ∈ s := hx
  let f := fun r : Fin (q.eval n.val) → Bool => sample (index n pp pk, List.ofFn r)
  let g := fun r => decide (f r = x)
  let k := (Finset.univ.filter fun r => g r = true).card
  have hmass : winProb ((uniformOfFinset s hne').map (fun z => decide (z = x))) =
      (s.card : ℝ)⁻¹ := by
    rw [winProb, PMF.map_apply, tsum_eq_single x]
    · simp [hx']
    · intro z hz
      simp [hz]
  have hpush : (uniformOfFintype (Fin (q.eval n.val) → Bool)).map f = uniformOfFinset s hne' := by
    simpa only [PMF.map_comp, Function.comp_def, f, s] using hlaw
  rw [← hpush, PMF.map_comp, winProb_map_uniform] at hmass
  change (k : ℝ) / Fintype.card (Fin (q.eval n.val) → Bool) = (s.card : ℝ)⁻¹ at hmass
  simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, Nat.cast_pow,
    Nat.cast_ofNat] at hmass
  have hcard : (s.card : ℝ) ≠ 0 := by exact_mod_cast (Finset.card_ne_zero.mpr ⟨x, hx⟩)
  have heq : (2 : ℝ) ^ q.eval n.val = s.card * k := by
    field_simp [hcard] at hmass
    linarith
  exact ⟨k, by exact_mod_cast heq⟩

/-- **Bounded-coin trapdoor permutation scheme.** A trapdoor function scheme in the exact
bounded-coin model whose codomain equals its domain at every generated public context. The
left inverse therefore makes the public map a permutation of that finite set. One-wayness is
a separate property of the keyed experiment, not a consequence of correctness. -/
def IsBoundedCoinPermutationScheme : Prop :=
  S.IsFunctionScheme ∧ ∀ (n : ℕ+) (pp pk sk), S.Generated n pp pk sk →
    S.codomain (index n pp pk) = S.domain (index n pp pk)

/-- **The one-way experiment.** For a family with a nonempty domain at every generated context,
draw the system parameter and the pair of keys from their specified laws. Conditional on them,
draw a uniform domain element and independent uniform adversary bits. The adversary receives the
unary security parameter, system parameter, public key, public image and its own bits. It wins
exactly when its output string equals the sampled element. -/
noncomputable def oneWayGame
    (hne : ∀ n pp pk sk, S.Generated n pp pk sk → (S.domain (index n pp pk)).Nonempty)
    (A : Index × Bits × Bits → Bits) (n : ℕ+) (m : ℕ) : PMF Bool :=
  (S.setup n).bindOnSupport fun pp hpp =>
    (S.keys n pp).bindOnSupport fun (pk, sk) hk =>
      let pub := index n pp pk
      (uniformOfFinset (S.domain pub) (hne n pp pk sk ⟨hpp, hk⟩)).bind fun x =>
        (coins m).map fun r => decide (A (pub, S.eval (pub, x), r) = x)

/-- **Computational one-wayness of a trapdoor function scheme.** For every polynomial coin
budget and every single polynomial-time bitstring algorithm, the success probability in the
keyed one-way experiment is negligible as the positive security parameter grows. Its value at
zero is extended by zero for the natural-number negligibility predicate. -/
def IsOneWay (h : S.IsFunctionScheme) : Prop :=
  ∀ (q : Polynomial ℕ) (A : Index × Bits × Bits → Bits), IsPolyTime A → NegligibleAdv fun n =>
    if hn : 0 < n then winProb (S.oneWayGame h.domain_nonempty A ⟨n, hn⟩ (q.eval n)) else 0

end Family

end Cslib.Crypto.PublicKey.Trapdoor
