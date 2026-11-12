/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Crypto.Protocols.Commitment.Binding

/-!
# Hash-based commitments: binding from collision resistance

For a keyed hash family `H : K → N × M → D` with public key `s`, the commitment to a message `m`
with a uniform nonce `r` is `H s (r, m)`, i.e. `H^s(r ‖ m)` with the nonce first. The pair
`(r, m)` models the concatenation `r ‖ m` for a fixed-length nonce, where splitting the string
back into nonce and message is unambiguous. It is packaged as a CSLib
`Cslib.Crypto.Protocols.Commitment.Scheme`.

* `collision_of_openings` (**binding extraction**): two openings `(m, r)` and `(m', r')` of one
  commitment with `m ≠ m'` are a collision `(r, m), (r', m')` of `H s`.
* `bindingAdvantage_le` (**computational binding from collision resistance**): in the generic
  binding experiment `Commitment.bindingGame gen (scheme H)`, where the key `s ← gen` comes from an
  arbitrary key-generation distribution and the adversary, with arbitrary coins, outputs a
  commitment with two openings, the success probability is at most the collision-finding advantage
  `collAdvantage gen H (reduction A)`; the reduction runs on the same key and the same coins.
* `perfectlyBinding_of_injective`: if `H s` is injective, the scheme is perfectly binding.
* Hiding is **not** unconditional, and is proved only from an explicit hypothesis on `H`:
  `NonceClose H s ε` says that, for every message, the digest of a uniform nonce and that message
  is within statistical distance `ε` of the uniform distribution on digests. Under it,
  `statisticallyHiding` gives statistical hiding with error `2 ε`, and `perfectlyHiding` gives
  perfect hiding when `ε = 0`. `NonceClose` fixes the key `s` and takes randomness only over the
  nonce, so it is a strong assumption on the fixed function `H s`; random-oracle hiding does not
  imply it. Hiding in the random-oracle model (Katz and Lindell, Section 5.6.5) averages over the
  oracle and needs a separate game that models oracle sampling and queries; it is deferred to the
  random-oracle lane.

The collision game `collGame` is a minimal local interface in the style of
`CSLibExt.Crypto.Framework.Games` (key generation `gen : PMF K`, adversary coins `coins : PMF R`).
Wave 3: unify with the Wave 1 HashFunction CRHF.

## References

* J. Katz and Y. Lindell, *Introduction to Modern Cryptography*, 2nd ed., CRC Press, 2014,
  Section 5.1 (collision resistance) and Section 5.6.5 (commitment schemes).
-/

@[expose] public section

namespace Cslib.Crypto.Protocols.Commitment.HashCommitment

open Cslib.Crypto.Framework

variable {K N M D : Type*}

/-! ### A local collision-resistance interface -/

/-- A collision of the keyed hash `H` under key `s`: two distinct inputs with the same digest.
Wave 3: unify with the Wave 1 HashFunction CRHF. -/
def IsCollision {X : Type*} (H : K → X → D) (s : K) (x x' : X) : Prop :=
  x ≠ x' ∧ H s x = H s x'

instance {X : Type*} [DecidableEq X] [DecidableEq D] (H : K → X → D) (s : K) (x x' : X) :
    Decidable (IsCollision H s x x') := by
  unfold IsCollision; infer_instance

/-- A collision finder for a keyed hash with keys in `K` and inputs in `X`: with coins
`r ← coins`, from the key it outputs two inputs. -/
structure CollFinder (K X R : Type*) where
  /-- The distribution of the collision finder's random coins. -/
  coins : PMF R
  /-- The collision finder, as a function of the key and its coins. -/
  run : K → R → X × X

section Collision

variable {X R : Type*} [DecidableEq X] [DecidableEq D]

/-- The collision-finding experiment `Hash-coll` (Katz and Lindell, Section 5.1): `s ← gen`,
`r ← A.coins`, and the experiment outputs `1` when the two inputs `A.run s r` collide under
`H s`. Wave 3: unify with the Wave 1 HashFunction CRHF. -/
noncomputable def collGame (gen : PMF K) (H : K → X → D) (A : CollFinder K X R) : PMF Bool :=
  gen.bind fun s => A.coins.map fun r => decide (IsCollision H s (A.run s r).1 (A.run s r).2)

/-- The collision-finding advantage: the success probability in `collGame`. -/
noncomputable def collAdvantage (gen : PMF K) (H : K → X → D) (A : CollFinder K X R) : ℝ :=
  winProb (collGame gen H A)

end Collision

/-! ### The scheme -/

/-- The commitment value `H^s(r ‖ m)`, with `r ‖ m` modeled by the pair `(r, m)`. -/
def commitValue (H : K → N × M → D) (s : K) (m : M) (r : N) : D := H s (r, m)

section Scheme

variable [Fintype N] [Nonempty N] [DecidableEq D]

/-- The hash-based commitment scheme with key `s` (Katz and Lindell, Section 5.6.5): commit to
`m` by sampling a uniform nonce `r` and publishing `H s (r, m)`; verification recomputes it. -/
noncomputable def scheme (H : K → N × M → D) (s : K) : Scheme M D N where
  commit m := (Cslib.Probability.PMF.uniformOfFintype N).map fun r => (commitValue H s m r, r)
  verify m c r := decide (commitValue H s m r = c)
  correct m c r hmem := by
    simp only [PMF.support_map, Set.mem_image, Prod.mk.injEq] at hmem
    obtain ⟨r', -, rfl, rfl⟩ := hmem
    simp

/-- An opening is accepted exactly when it recomputes the commitment. -/
@[simp]
theorem accepts_iff {H : K → N × M → D} {s : K} {m : M} {c : D} {r : N} :
    (scheme H s).Accepts m c r ↔ commitValue H s m r = c := by
  simp [Scheme.Accepts, scheme]

/-- If `H s` is injective, the hash commitment is perfectly binding. -/
theorem perfectlyBinding_of_injective {H : K → N × M → D} {s : K}
    (hinj : Function.Injective (H s)) : (scheme H s).PerfectlyBinding := by
  intro c m₀ r₀ m₁ r₁ h₀ h₁
  rw [accepts_iff, commitValue] at h₀ h₁
  exact (Prod.ext_iff.mp (hinj (h₀.trans h₁.symm))).2

/-! ### Hiding under an explicit hypothesis on `H` -/

/-- The digest of a uniform nonce and the message `m`. -/
noncomputable def nonceDigest (H : K → N × M → D) (s : K) (m : M) : PMF D :=
  (Cslib.Probability.PMF.uniformOfFintype N).map fun r => H s (r, m)

/-- The hiding hypothesis on `H`: for every message, the digest of a uniform nonce and that
message is `ε`-close to uniform on `D`. The key `s` is fixed and only the nonce is random, so this
is an assumption on the fixed function `H s`, not a consequence of collision resistance or of
random-oracle hiding (Katz and Lindell, Section 5.6.5). For example, with a one-element nonce
space and `D = Bool` every nonce digest is a point mass, at statistical distance `1 / 2` from
uniform, for every choice of `H s`. -/
def NonceClose [Fintype D] [Nonempty D] (H : K → N × M → D) (s : K) (ε : NNReal) : Prop :=
  ∀ m : M, Cslib.Probability.PMF.StatisticallyClose (nonceDigest H s m)
    (Cslib.Probability.PMF.uniformOfFintype D) ε

/-- The commitment distribution of `m` is the nonce digest of `m`. -/
theorem commitmentDist_eq (H : K → N × M → D) (s : K) (m : M) :
    (scheme H s).commitmentDist m = nonceDigest H s m := by
  rw [Scheme.commitmentDist, scheme, PMF.map_comp]
  rfl

/-- **Statistical hiding under `NonceClose`**: if every nonce digest is `ε`-close to uniform,
the hash commitment is statistically hiding with error `2 ε`. -/
theorem statisticallyHiding [Fintype D] [Nonempty D] {H : K → N × M → D} {s : K} {ε : NNReal}
    (hH : NonceClose H s ε) : (scheme H s).StatisticallyHiding (2 * ε) := fun m₀ m₁ => by
  rw [commitmentDist_eq, commitmentDist_eq, two_mul]
  exact (hH m₀).trans (hH m₁).symm

/-- **Perfect hiding under `NonceClose` with `ε = 0`**: if every nonce digest is exactly
uniform, the hash commitment is perfectly hiding. -/
theorem perfectlyHiding [Fintype D] [Nonempty D] {H : K → N × M → D} {s : K}
    (hH : NonceClose H s 0) : (scheme H s).PerfectlyHiding := by
  rw [Scheme.perfectlyHiding_iff_statisticallyHiding_zero]
  simpa using statisticallyHiding hH

end Scheme

/-! ### Binding from collision resistance -/

/-- **Binding extraction**: two openings of the same commitment to different messages form a
collision of `H s`. -/
theorem collision_of_openings {H : K → N × M → D} {s : K} {c : D} {m m' : M} {r r' : N}
    (hne : m ≠ m') (h₁ : commitValue H s m r = c) (h₂ : commitValue H s m' r' = c) :
    IsCollision H s (r, m) (r', m') :=
  ⟨fun h => hne (Prod.ext_iff.mp h).2, h₁.trans h₂.symm⟩

section Binding

variable [Fintype N] [Nonempty N] [DecidableEq N] [DecidableEq M] [DecidableEq D] {R : Type*}

/-- The collision finder built from a binding adversary: on the same key and the same coins,
output the two hash inputs `(r, m)` and `(r', m')` of its openings. -/
def reduction (A : BindingAdversary K M D N R) : CollFinder K (N × M) R where
  coins := A.coins
  run s t := (((A.run s t).2.1.2, (A.run s t).2.1.1), ((A.run s t).2.2.2, (A.run s t).2.2.1))

/-- **Computational binding of hash commitments from collision resistance**: for every key
distribution `gen` and every binding adversary (with arbitrary coins), the success probability in
the binding experiment for `scheme H` is at most the collision-finding advantage of
`reduction A` (Katz and Lindell, Section 5.6.5). -/
theorem bindingAdvantage_le (gen : PMF K) (H : K → N × M → D) (A : BindingAdversary K M D N R) :
    bindingAdvantage gen (scheme H) A ≤ collAdvantage gen H (reduction A) := by
  refine winProb_bind_map_mono _ _ fun s _ t hw => ?_
  obtain ⟨h₁, h₂, hne⟩ := of_decide_eq_true hw
  exact decide_eq_true (collision_of_openings hne (accepts_iff.mp h₁) (accepts_iff.mp h₂))

end Binding

end Cslib.Crypto.Protocols.Commitment.HashCommitment
