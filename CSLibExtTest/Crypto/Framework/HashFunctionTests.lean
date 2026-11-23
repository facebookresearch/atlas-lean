/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Crypto.Protocols.Commitment.HashCommitment
public import Mathlib.Tactic.NormNum

/-!
# Tests for the Framework hash-function games

Toy computations for `CSLibExt.Crypto.Framework.HashFunction` and for the hash-commitment binding bound.

* **Injective hash.** `succHash` (`x ↦ x + 1` on `ZMod 5`) is injective, so every collision
  finder has advantage `0` (`collAdvantage_eq_zero_of_injective`); computed directly, the finder
  `pairFinder`, which outputs `(0, 1)`, loses.
* **Colliding hashes.** Against the constant hash `constHash`, `pairFinder` always wins: advantage
  `1` (`collAdvantage_eq_one_of_forall`). Against `keyedHash`, whose uniform key makes it constant
  under `true` and the identity under `false`, it wins exactly for the key `true`: advantage `1/2`.
* **Target collision resistance.** `tcrAdv` commits to `0` before it sees the key and then answers
  `1`. Its collision finder `tcrToColl tcrAdv` is `pairFinder`, so its target-collision advantage
  against `keyedHash` is `1/2` (`tcrAdvantage_eq_collAdvantage`).
* **Hash-commitment binding.** For the commitment `H (r, m) = r + m` on `ZMod 5`, the binding
  adversary `openTwice`, which opens `3` as `(2, 1)` and as `(1, 2)`, always wins. Through
  `bindingAdvantage_le`, its reduction is a Framework collision finder with advantage `1`.
-/

@[expose] public section

namespace Cslib.Crypto.FrameworkTests.HashFunction

open Cslib.Crypto.Framework

/-! ### An injective hash -/

/-- The injective hash `x ↦ x + 1` on `ZMod 5`, with a single key. -/
noncomputable def succHash : HashFamily Unit (ZMod 5) (ZMod 5) := ⟨PMF.pure (), fun _ x => x + 1⟩

/-- The collision finder that outputs `(0, 1)` under every key. -/
noncomputable def pairFinder {K : Type} : CollisionFinder K (ZMod 5) Unit :=
  ⟨PMF.pure (), fun _ _ => (0, 1)⟩

/-- No finder finds a collision of the injective hash. -/
example {R : Type} (A : CollisionFinder Unit (ZMod 5) R) : collAdvantage succHash A = 0 :=
  collAdvantage_eq_zero_of_injective succHash (fun _ => add_left_injective 1) A

/-- Computed directly: `(0, 1)` is not a collision of `x ↦ x + 1`. -/
theorem collAdvantage_succHash_pairFinder : collAdvantage succHash pairFinder = 0 := by
  rw [collAdvantage, collGame]
  simp only [succHash, pairFinder, PMF.pure_bind, PMF.pure_map]
  have h : ¬ IsCollision (fun x : ZMod 5 => x + 1) (0, 1) := by decide
  simp [h]

/-! ### Colliding hashes -/

/-- The constant hash on `ZMod 5`, with a single key. -/
noncomputable def constHash : HashFamily Unit (ZMod 5) (ZMod 5) := ⟨PMF.pure (), fun _ _ => 0⟩

/-- Every output of `pairFinder` collides under the constant hash: advantage `1`. -/
theorem collAdvantage_constHash_pairFinder : collAdvantage constHash pairFinder = 1 :=
  collAdvantage_eq_one_of_forall constHash pairFinder fun _ _ =>
    ⟨show (0 : ZMod 5) ≠ 1 by decide, rfl⟩

/-- A keyed hash on `ZMod 5` with a uniform key: constant under the key `true`, the identity under
the key `false`. -/
noncomputable def keyedHash : HashFamily Bool (ZMod 5) (ZMod 5) :=
  ⟨Cslib.Probability.PMF.uniformOfFintype Bool, fun s x => if s then 0 else x⟩

/-- `pairFinder` finds a collision only under the key `true`: advantage `1/2`. -/
theorem collAdvantage_keyedHash_pairFinder : collAdvantage keyedHash pairFinder = 1 / 2 := by
  rw [collAdvantage, collGame]
  simp only [keyedHash, pairFinder, PMF.pure_map]
  change winProb ((Cslib.Probability.PMF.uniformOfFintype Bool).map _) = 1 / 2
  rw [winProb_map_uniform]
  norm_num
  decide

/-! ### Target collision resistance -/

/-- Commit to `0` before seeing the key, then answer `1`. -/
noncomputable def tcrAdv : TCRAdversary Bool (ZMod 5) Unit :=
  ⟨PMF.pure (), fun _ => 0, fun _ _ => 1⟩

/-- Committing and then answering is a particular collision finder: `pairFinder`. -/
theorem tcrToColl_tcrAdv : tcrToColl tcrAdv = pairFinder := rfl

/-- The target-collision advantage of `tcrAdv` is the collision advantage of `pairFinder`. -/
theorem tcrAdvantage_keyedHash_tcrAdv : tcrAdvantage keyedHash tcrAdv = 1 / 2 := by
  rw [tcrAdvantage_eq_collAdvantage, tcrToColl_tcrAdv, collAdvantage_keyedHash_pairFinder]

/-! ### Hash-commitment binding -/

section Binding

open Cslib.Crypto.Protocols.Commitment

/-- The toy hash `H (r, m) = r + m` on `ZMod 5`, with a single key. -/
def addHash : Unit → ZMod 5 × ZMod 5 → ZMod 5 := fun _ x => x.1 + x.2

/-- A binding adversary that always opens `3` as `(2, 1)` and as `(1, 2)`. -/
noncomputable def openTwice : BindingAdversary Unit (ZMod 5) (ZMod 5) (ZMod 5) Unit where
  coins := PMF.pure ()
  run _ _ := (3, (2, 1), (1, 2))

/-- `openTwice` always wins the binding game. -/
theorem bindingAdvantage_openTwice :
    bindingAdvantage (PMF.pure ()) (HashCommitment.scheme addHash) openTwice = 1 := by
  rw [bindingAdvantage, bindingGame, PMF.pure_bind, openTwice, PMF.pure_map, winProb_pure]
  split_ifs with hw
  · rfl
  · exact (hw (by decide)).elim

/-- The reduction of `openTwice` is a Framework collision finder against
`⟨PMF.pure (), addHash⟩` with advantage `1`. -/
theorem framework_collAdvantage_reduction_openTwice :
    collAdvantage ⟨PMF.pure (), addHash⟩ (HashCommitment.reduction openTwice) =
      1 :=
  le_antisymm (winProb_le_one _)
    (bindingAdvantage_openTwice ▸
      HashCommitment.bindingAdvantage_le ⟨PMF.pure (), addHash⟩ openTwice)


end Binding

end Cslib.Crypto.FrameworkTests.HashFunction
