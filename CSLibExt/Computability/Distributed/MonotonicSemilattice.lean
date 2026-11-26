/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Order.Defs.Lattice

/-!
# Monotonic semilattice objects

The state-based object interface and the local laws from Shapiro, Preguiça, Baquero, and Zawirski,
*Conflict-free replicated data types*, INRIA RR-7687, §§2.1 and 2.3, Definition 2.4.
The laws do not assert delivery or convergence of executions.
-/

namespace Cslib.Distributed

universe u v w x

/-- The local interface of a state-based replicated object. A method index includes its arguments.
Each query returns a result and a post-state; the result type can depend on the method. Updates
operate on one replica, and `merge` takes the local state followed by the received state.

Source: Shapiro, Preguiça, Baquero, and Zawirski, *Conflict-free replicated data types*,
INRIA RR-7687, §2.1. -/
public structure StateBasedReplicatedObject (State : Type u) (Query : Type v)
    (Result : Query → Type w) (Update : Type x) where
  /-- The designated initial state of each replica. -/
  initial : State
  /-- The result and post-state of invoking a query. -/
  query : (q : Query) → State → Result q × State
  /-- The new local state after invoking an update. -/
  update : Update → State → State
  /-- The new local state after receiving another replica's state. -/
  merge : State → State → State

/-- A state-based object on a join-semilattice is monotonic when merge is join, every update
is inflationary, and a query's post-state gives the same results as its pre-state for every
query. This last condition concerns observations, not equality of the two states. Neither
monotonicity of each update function nor a least initial state is required.

Source: Shapiro, Preguiça, Baquero, and Zawirski, *Conflict-free replicated data types*,
INRIA RR-7687, Definition 2.4. -/
@[expose] public def StateBasedReplicatedObject.IsMonotonicSemilattice {State : Type u}
    {Query : Type v} {Result : Query → Type w} {Update : Type x} [SemilatticeSup State]
    (obj : StateBasedReplicatedObject State Query Result Update) : Prop :=
  (∀ s t, obj.merge s t = s ⊔ t) ∧
    (∀ method s, s ≤ obj.update method s) ∧
    (∀ q s q', (obj.query q' (obj.query q s).2).1 = (obj.query q' s).1)

end Cslib.Distributed
