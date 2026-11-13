/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Crypto.Framework.HashFunction
public import CSLibExt.Crypto.Protocols.Commitment.HashCommitment

/-!
# Hash commitments and the Framework collision game

`CSLibExt.Crypto.Protocols.Commitment.HashCommitment` proves binding against its own local
collision interface: `HashCommitment.IsCollision`, `HashCommitment.CollFinder`,
`HashCommitment.collGame` and `HashCommitment.collAdvantage`. This file identifies that interface
with the Framework's collision game of `CSLibExt.Crypto.Framework.HashFunction` (`HashFamily`,
`CollisionFinder`, `Framework.collGame`, `Framework.collAdvantage`), so that a bound stated with
either game transfers to the other.

* `CollFinder.toCollisionFinder` and `CollFinder.ofCollisionFinder` convert between the two
  finder types: the same coins, with the field `run` renamed `find`. The conversions are mutually
  inverse.
* `isCollision_iff_framework`: the local collision predicate is `Framework.IsCollision` of `H s`
  at the pair of inputs.
* `framework_collGame_toCollisionFinder` and `framework_collAdvantage_toCollisionFinder`: for the
  hash family `⟨gen, H⟩`, the Framework game of a converted finder is the local game, and
  `collAdvantage_ofCollisionFinder` is the converse.
* `bindingAdvantage_le_framework_collAdvantage`: `bindingAdvantage_le` with the Framework
  collision advantage, so the binding advantage of the hash commitment is at most the advantage of
  a Framework collision finder against `⟨gen, H⟩`.
-/

@[expose] public section

namespace Cslib.Crypto.Protocols.Commitment.HashCommitment

variable {K N M D X R : Type*}

/-! ### Converting collision finders -/

/-- A local collision finder as a Framework `CollisionFinder`: the same coins, with `run` as
`find`. -/
def CollFinder.toCollisionFinder (A : CollFinder K X R) : Framework.CollisionFinder K X R :=
  ⟨A.coins, A.run⟩

/-- A Framework `CollisionFinder` as a local collision finder: the same coins, with `find` as
`run`. -/
def CollFinder.ofCollisionFinder (A : Framework.CollisionFinder K X R) : CollFinder K X R :=
  ⟨A.coins, A.find⟩

@[simp] theorem CollFinder.ofCollisionFinder_toCollisionFinder (A : CollFinder K X R) :
    CollFinder.ofCollisionFinder A.toCollisionFinder = A :=
  rfl

@[simp] theorem CollFinder.toCollisionFinder_ofCollisionFinder
    (A : Framework.CollisionFinder K X R) :
    (CollFinder.ofCollisionFinder A).toCollisionFinder = A :=
  rfl

/-- The local collision predicate is the Framework one at the pair of inputs. -/
theorem isCollision_iff_framework (H : K → X → D) (s : K) (x x' : X) :
    IsCollision H s x x' ↔ Framework.IsCollision (H s) (x, x') :=
  Iff.rfl

/-! ### The two games agree -/

section Games

variable [DecidableEq X] [DecidableEq D]

/-- The Framework collision game of the hash family `⟨gen, H⟩` against a converted finder is the
local collision game. -/
theorem framework_collGame_toCollisionFinder (gen : PMF K) (H : K → X → D)
    (A : CollFinder K X R) :
    Framework.collGame ⟨gen, H⟩ A.toCollisionFinder = collGame gen H A :=
  rfl

/-- The Framework collision advantage against `⟨gen, H⟩` of a converted finder is the local
collision advantage. -/
theorem framework_collAdvantage_toCollisionFinder (gen : PMF K) (H : K → X → D)
    (A : CollFinder K X R) :
    Framework.collAdvantage ⟨gen, H⟩ A.toCollisionFinder = collAdvantage gen H A := by
  rw [Framework.collAdvantage, framework_collGame_toCollisionFinder, collAdvantage]

/-- The local collision advantage of a converted Framework finder is its Framework collision
advantage. -/
theorem collAdvantage_ofCollisionFinder (Hf : Framework.HashFamily K X D)
    (A : Framework.CollisionFinder K X R) :
    collAdvantage Hf.gen Hf.hash (CollFinder.ofCollisionFinder A) =
      Framework.collAdvantage Hf A := by
  rw [← framework_collAdvantage_toCollisionFinder, CollFinder.toCollisionFinder_ofCollisionFinder]

end Games

/-! ### Binding from Framework collision resistance -/

/-- **Computational binding from Framework collision resistance**: `bindingAdvantage_le` with the
Framework collision advantage of the hash family `⟨gen, H⟩`. -/
theorem bindingAdvantage_le_framework_collAdvantage [Fintype N] [Nonempty N] [DecidableEq N]
    [DecidableEq M] [DecidableEq D] (gen : PMF K) (H : K → N × M → D)
    (A : BindingAdversary K M D N R) :
    bindingAdvantage gen (scheme H) A ≤
      Framework.collAdvantage ⟨gen, H⟩ (reduction A).toCollisionFinder := by
  rw [framework_collAdvantage_toCollisionFinder]
  exact bindingAdvantage_le gen H A

end Cslib.Crypto.Protocols.Commitment.HashCommitment
