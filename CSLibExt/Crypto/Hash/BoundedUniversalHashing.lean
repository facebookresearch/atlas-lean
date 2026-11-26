/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Card

/-!
# Bounded universal hash functions

An indexed family of hashes has a collision bound if each pair of distinct inputs
collides for at most the specified fraction of keys. This is a bound for a uniform
choice of key, not for a pair chosen after seeing the key.

See Boneh and Shoup, *A Graduate Course in Applied Cryptography*, version 0.4,
Definition 7.2 and equation (7.1).
-/

@[expose] public section

namespace Cslib.Crypto.BoundedUniversalHashing

variable {Key Input Output : Type*} [Fintype Key]

open Classical in
/-- **Collision probability under a uniform key.** Let `H` be a keyed hash function
with finite key type $K$, and let $x$ and $y$ be inputs. If $K$ is nonempty, the
probability that the hashes of $x$ and $y$ agree under a uniform key is
$|\{k \in K : H(k,x) = H(k,y)\}|/|K|$. Each key counts separately even if two
keys induce the same function. On the empty key type the ratio returns zero by
convention; it does not describe a uniform distribution there. -/
noncomputable def collisionProbability (hash : Key → Input → Output) (x y : Input) : ℝ :=
  ((Finset.univ.filter fun k => hash k x = hash k y).card : ℝ) / Fintype.card Key

/-- A keyed family is `ε`-bounded universal if its finite key type is nonempty, `ε` is
nonnegative, and every pair of distinct inputs collides with probability at most `ε`
under a uniform key. Neither the input nor the output type is required to be finite. -/
def IsBoundedUniversal (hash : Key → Input → Output) (ε : ℝ) : Prop :=
  Nonempty Key ∧ 0 ≤ ε ∧ ∀ x y : Input, x ≠ y → collisionProbability hash x y ≤ ε

end Cslib.Crypto.BoundedUniversalHashing
