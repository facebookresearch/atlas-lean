/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Crypto.Framework.Asymptotic

/-!
# Collision-resistant and target-collision-resistant hash functions

A **keyed hash function** is modelled here as a key-generation distribution `gen : PMF K`
together with a deterministic keyed function `hash : K → X → Y` (after Katz and Lindell,
Definition 5.1, without its efficiency and length conditions; see below). The two security games
of this file are Framework games: every experiment is a `PMF Bool`, every adversary carries its
coins as a distribution, and every advantage is a `winProb`.

* `collGame H A`, `collAdvantage` (the experiment `Hash-coll` of Katz and Lindell,
  Definition 5.2): `s ← Gen`, the collision finder gets `s` and outputs `(x, x')`; it wins when
  `x ≠ x'` and `H^s(x) = H^s(x')`.
* `tcrGame H A`, `tcrAdvantage` (**target collision resistance**, the universal one-way hash
  functions of Naor and Yung; Katz and Lindell, Section 5.1, "Weaker notions of security"):
  the adversary first commits to a message `x`, **then** receives the key `s`, and must output
  `x' ≠ x` with `H^s(x') = H^s(x)`.
* `tcrAdvantage_eq_collAdvantage`: committing and then finding a collision is a particular
  collision finder (`tcrToColl`), so `tcrAdvantage H A = collAdvantage H (tcrToColl A)`;
  collision resistance implies target collision resistance (Katz and Lindell, Section 5.1).
* `collAdvantage_eq_zero_of_injective`, `collAdvantage_eq_one_of_forall`: an injective hash has
  no collisions, and a finder that always outputs a collision has advantage `1`.
* `CollisionResistant`, `TargetCollisionResistant`: the asymptotic notions for a family of keyed
  hash functions indexed by the security parameter, as `Framework.AsymptoticallySecure` with an
  admissible class of adversary families passed as an argument (a collision finder makes no
  oracle queries, so no query-count class applies; compare `Framework.PubCPASecure`).
  `TargetCollisionResistant.of_collisionResistant` is the asymptotic implication. As for every
  `Framework.Asymptotic` instance, the input and coin types must be nonempty,
  `[∀ n, Nonempty (X n)]` and `[∀ n, Nonempty (R n)]`: with no input there is no output pair,
  and with no coins there is no `PMF`, so there would be no adversary and the notion would hold
  vacuously (even for a constant hash). `CollisionFinder.nonempty` and `TCRAdversary.nonempty`
  give an adversary under these hypotheses.

**Abstract keyed functions; efficiency and compression are not modelled.** `HashFamily` is a keyed
function on arbitrary types, not Definition 5.1 verbatim, and `CollisionResistant` and
`TargetCollisionResistant` are relative to the caller's admissible class. The source conditions
they omit:

* `Gen` and `H` are **polynomial-time** algorithms (probabilistic and deterministic);
* keys, inputs and outputs are **bit strings**, the output length `ℓ(n)` is fixed, and a
  fixed-length hash function **compresses**: its inputs have length `ℓ'(n) > ℓ(n)`;
* collision finders and target-collision adversaries are **probabilistic polynomial-time**.

The first two constrain the family and are not imposed at all: a noncomputable family, or a
non-compressing one, can satisfy `CollisionResistant`. In particular an injective family has no
collisions (`collAdvantage_eq_zero_of_injective`), so it is collision resistant against every
adversary family, although it does not compress. The games are therefore the generic collision
and target-collision games of a keyed function; compression is a property of the instance.
The third condition is whatever `Admissible` encodes: the framework has no polynomial-time model
for these adversaries (see "What is deferred" in `CSLibExt.Crypto.Framework.Asymptotic`).

These are the Framework's hash-function games: `HashFamily`, `CollisionFinder`, `TCRAdversary`
and the games live in the namespace `Cslib.Crypto.Framework` next to the scheme games of
`CSLibExt.Crypto.Framework.Games`, and the asymptotic notions are instances of
`Framework.AsymptoticallySecure`. Hash commitments
(`CSLibExt.Crypto.Protocols.Commitment.HashCommitment`) prove binding against their own local
collision game; `CSLibExt.Crypto.Protocols.Commitment.HashCommitmentFramework` identifies that
game with `collGame` and restates the binding bound with `collAdvantage`
(`HashCommitment.bindingAdvantage_le`).
The older unkeyed compression-collision game `Cslib.Crypto.MerkleDamgard.compressionCollisionGame`
predates the framework; its predicate `MerkleDamgard.IsCollision` has the same definition as
`IsCollision`, but its adversary has uniform coins and an optional output, and the two games are
not related formally here.

## References

* J. Katz and Y. Lindell, *Introduction to Modern Cryptography*, 2nd ed., CRC Press, 2014,
  Section 5.1, Definitions 5.1 and 5.2.
* M. Naor and M. Yung, *Universal one-way hash functions and their cryptographic applications*,
  STOC 1989.
-/

@[expose] public section

namespace Cslib.Crypto.Framework

/-! ### Keyed hash functions and the two adversaries -/

/-- A keyed hash function, abstractly (after Katz and Lindell, Definition 5.1): a key-generation
distribution and a deterministic keyed function `H^s : X → Y` on arbitrary types. The source's
efficiency, bit-string and compression conditions are not imposed (see the module
documentation). -/
structure HashFamily (K X Y : Type*) where
  /-- Key generation `Gen`. -/
  gen : PMF K
  /-- The keyed function `H^s`. -/
  hash : K → X → Y

/-- A pair of distinct inputs on which `f` agrees. -/
def IsCollision {X Y : Type*} (f : X → Y) (p : X × X) : Prop := p.1 ≠ p.2 ∧ f p.1 = f p.2

instance {X Y : Type*} [DecidableEq X] [DecidableEq Y] (f : X → Y) (p : X × X) :
    Decidable (IsCollision f p) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- A collision finder (the adversary of Katz and Lindell, Definition 5.2): with coins
`r ← coins` and the key `s`, it outputs two inputs. -/
structure CollisionFinder (K X R : Type*) where
  /-- The distribution of the finder's random coins. -/
  coins : PMF R
  /-- The finder, as a function of the key and its coins. -/
  find : K → R → X × X

/-- A target-collision adversary: with coins `r ← coins` it first commits to a target `commit r`
without seeing the key, then receives the key `s` and outputs a second input `find s r`. -/
structure TCRAdversary (K X R : Type*) where
  /-- The distribution of the adversary's random coins. -/
  coins : PMF R
  /-- The target message, chosen before the key is known. -/
  commit : R → X
  /-- The second message, chosen after the key is known. -/
  find : K → R → X

/-! ### The games -/

section Games

variable {K X Y R : Type*} [DecidableEq X] [DecidableEq Y]

/-- **`Hash-coll`** (Katz and Lindell, Definition 5.2): `s ← Gen`, the finder outputs `(x, x')`,
and the experiment outputs `1` when `x ≠ x'` and `H^s(x) = H^s(x')`. -/
noncomputable def collGame (H : HashFamily K X Y) (A : CollisionFinder K X R) : PMF Bool :=
  H.gen.bind fun s => A.coins.map fun r => decide (IsCollision (H.hash s) (A.find s r))

/-- The collision-finding advantage `Pr[Hash-coll = 1]`. -/
noncomputable def collAdvantage (H : HashFamily K X Y) (A : CollisionFinder K X R) : ℝ :=
  winProb (collGame H A)

/-- **Target collision resistance** (universal one-way hashing; Katz and Lindell, Section 5.1):
the adversary commits to `x`, then `s ← Gen` is revealed and it outputs `x'`; the experiment
outputs `1` when `x' ≠ x` and `H^s(x) = H^s(x')`. -/
noncomputable def tcrGame (H : HashFamily K X Y) (A : TCRAdversary K X R) : PMF Bool :=
  H.gen.bind fun s => A.coins.map fun r => decide (IsCollision (H.hash s) (A.commit r, A.find s r))

/-- The target-collision advantage `Pr[tcrGame = 1]`. -/
noncomputable def tcrAdvantage (H : HashFamily K X Y) (A : TCRAdversary K X R) : ℝ :=
  winProb (tcrGame H A)

/-- A target-collision adversary is a collision finder that outputs its committed target and its
second message. -/
def tcrToColl (A : TCRAdversary K X R) : CollisionFinder K X R where
  coins := A.coins
  find s r := (A.commit r, A.find s r)

/-- **Collision resistance implies target collision resistance** (Katz and Lindell, Section 5.1):
the target-collision experiment of `A` is literally the collision experiment of `tcrToColl A`. -/
theorem tcrAdvantage_eq_collAdvantage (H : HashFamily K X Y) (A : TCRAdversary K X R) :
    tcrAdvantage H A = collAdvantage H (tcrToColl A) := rfl

/-- A two-stage experiment whose outcome is constant has that outcome as its distribution. -/
private theorem bind_map_const {S R : Type*} (μ : PMF S) (ν : PMF R) {f : S → R → Bool}
    (b : Bool) (hf : ∀ s r, f s r = b) : (μ.bind fun s => ν.map (f s)) = PMF.pure b := by
  have : (fun s => ν.map (f s)) = fun _ => PMF.pure b :=
    funext fun s => by rw [show f s = Function.const R b from funext (hf s), PMF.map_const]
  rw [this, PMF.bind_const]

/-- An **injective** hash function has no collisions: every finder has advantage `0`. -/
theorem collAdvantage_eq_zero_of_injective (H : HashFamily K X Y)
    (hinj : ∀ s, Function.Injective (H.hash s)) (A : CollisionFinder K X R) :
    collAdvantage H A = 0 := by
  rw [collAdvantage, collGame, bind_map_const _ _ false fun s r => ?_, winProb_pure]
  · rfl
  · exact decide_eq_false fun h => h.1 (hinj s h.2)

/-- A finder that outputs a collision for every key and every choice of coins has advantage `1`. -/
theorem collAdvantage_eq_one_of_forall (H : HashFamily K X Y) (A : CollisionFinder K X R)
    (hA : ∀ s r, IsCollision (H.hash s) (A.find s r)) : collAdvantage H A = 1 := by
  rw [collAdvantage, collGame, bind_map_const _ _ true fun s r => decide_eq_true (hA s r),
    winProb_pure]
  rfl

end Games

/-! ### Asymptotic notions -/

section Asymptotic

variable {K X Y : ℕ → Type*} [∀ n, DecidableEq (X n)] [∀ n, DecidableEq (Y n)]

/-- **Collision resistance** of a family of keyed hash functions (Katz and Lindell,
Definition 5.2): every admissible family of collision finders has negligible advantage. A finder
makes no oracle queries, so the admissible class is an argument (eventually: probabilistic
polynomial time); with the class of all families this is security against unbounded finders. The
input and coin types must be nonempty, or there would be no finder and the notion would hold
vacuously (`CollisionFinder.nonempty`); whether some family is admissible depends on
`Admissible`. No efficiency or compression condition is imposed on `H`, so an injective family is
collision resistant (see the module documentation). -/
@[nolint unusedArguments]
def CollisionResistant (H : (n : ℕ) → HashFamily (K n) (X n) (Y n)) (R : ℕ → Type*)
    [∀ n, Nonempty (X n)] [∀ n, Nonempty (R n)]
    (Admissible : ((n : ℕ) → CollisionFinder (K n) (X n) (R n)) → Prop) : Prop :=
  AsymptoticallySecure (fun n A => collAdvantage (H n) A) Admissible

/-- **Target collision resistance** (universal one-way hashing) of a family of keyed hash
functions, against an admissible class of target-collision adversary families. The input and
coin types must be nonempty (`TCRAdversary.nonempty`). -/
@[nolint unusedArguments]
def TargetCollisionResistant (H : (n : ℕ) → HashFamily (K n) (X n) (Y n)) (R : ℕ → Type*)
    [∀ n, Nonempty (X n)] [∀ n, Nonempty (R n)]
    (Admissible : ((n : ℕ) → TCRAdversary (K n) (X n) (R n)) → Prop) : Prop :=
  AsymptoticallySecure (fun n A => tcrAdvantage (H n) A) Admissible

/-- **Collision resistance implies target collision resistance**, asymptotically: if the
reduction `tcrToColl` maps admissible target-collision adversaries to admissible collision
finders, collision resistance gives target collision resistance with the same advantage. -/
theorem TargetCollisionResistant.of_collisionResistant
    {H : (n : ℕ) → HashFamily (K n) (X n) (Y n)} {R : ℕ → Type*}
    [∀ n, Nonempty (X n)] [∀ n, Nonempty (R n)]
    {AdmT : ((n : ℕ) → TCRAdversary (K n) (X n) (R n)) → Prop}
    {AdmC : ((n : ℕ) → CollisionFinder (K n) (X n) (R n)) → Prop}
    (hadm : ∀ A, AdmT A → AdmC fun n => tcrToColl (A n))
    (h : CollisionResistant H R AdmC) : TargetCollisionResistant H R AdmT :=
  AsymptoticallySecure.of_reduction (fun A n => tcrToColl (A n)) hadm negligibleAdv_zero
    (fun A _ n => by rw [tcrAdvantage_eq_collAdvantage, add_zero]) h

end Asymptotic

/-! ### Non-vacuity -/

/-- With an input and a coin value there is a collision finder (it outputs `(x, x)`), so
`CollisionResistant` is not vacuous for the class of all families. -/
theorem CollisionFinder.nonempty {K X R : Type*} [Nonempty X] [Nonempty R] :
    Nonempty (CollisionFinder K X R) := by
  obtain ⟨x⟩ := ‹Nonempty X›
  obtain ⟨r⟩ := ‹Nonempty R›
  exact ⟨⟨PMF.pure r, fun _ _ => (x, x)⟩⟩

/-- With an input and a coin value there is a target-collision adversary (it commits to `x` and
answers `x`), so `TargetCollisionResistant` is not vacuous for the class of all families. -/
theorem TCRAdversary.nonempty {K X R : Type*} [Nonempty X] [Nonempty R] :
    Nonempty (TCRAdversary K X R) := by
  obtain ⟨x⟩ := ‹Nonempty X›
  obtain ⟨r⟩ := ‹Nonempty R›
  exact ⟨⟨PMF.pure r, fun _ => x, fun _ _ => x⟩⟩

end Cslib.Crypto.Framework
