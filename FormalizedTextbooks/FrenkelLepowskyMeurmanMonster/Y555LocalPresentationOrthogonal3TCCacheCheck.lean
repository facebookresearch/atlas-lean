/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact actual-source and matrix-recurrence predicates for representative prefix caches. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationOrthogonal3TCCacheData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationTransportProgram
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationRawInstructionEquality

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The exact actual source-program index of a finite representative word-prefix cache entry. -/
def y322Orthogonal3TCCacheReference (i : Fin 7253) : Fin 48640 :=
  ⟨38540 + (y322Orthogonal3TCCacheNode i).val, by omega⟩

/-- Check literal source instructions, strict prefix ancestry, and exact finite matrix products. -/
def y322Orthogonal3TCCacheCheckAt (index : ℕ) : Prop :=
  if h : index < 7253 then
    let i : Fin 7253 := ⟨index, h⟩
    let p := y322Orthogonal3TCCacheParent i
    if index = 0 then
      y322Orthogonal3TCCacheNode i = 0 ∧
      y322InstructionRaw (y322TransportProgram (y322Orthogonal3TCCacheReference i)) = .one ∧
      y322Orthogonal3TCCacheMatrix i = 1 ∧ y322Orthogonal3TCCacheInverse i = 1
    else
      p.val < i.val ∧ (y322Orthogonal3TCCacheNode p).val <
        (y322Orthogonal3TCCacheNode i).val ∧
      y322InstructionRaw (y322TransportProgram (y322Orthogonal3TCCacheReference i)) =
        .appendGenerator (38540 + (y322Orthogonal3TCCacheNode p).val)
          (y322Orthogonal3TCCacheGenerator i) ∧
      y322Orthogonal3TCCacheMatrix i = y322Orthogonal3TCCacheMatrix p *
        y322Orthogonal3Reflection (y322Orthogonal3TCCacheGenerator i) ∧
      y322Orthogonal3TCCacheInverse i =
        y322Orthogonal3Reflection (y322Orthogonal3TCCacheGenerator i) *
          y322Orthogonal3TCCacheInverse p
  else True

/-- The exact source and finite matrix cache check is decidable. -/
instance y322Orthogonal3TCCacheCheckAtDecidable (index : ℕ) :
    Decidable (y322Orthogonal3TCCacheCheckAt index) := by
  unfold y322Orthogonal3TCCacheCheckAt
  split
  · split <;> infer_instance
  · infer_instance

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
