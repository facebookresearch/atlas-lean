/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Languages.RegularShuffle
public import CSLibExt.Computability.Languages.Finite

/-!
# Tests for shuffle and cyclic shift

* `[true, false]` and `[false, true]` both interleave `[true]` with `[false]`; `[true, true]`
  does not.
* The shuffle of `{[true]}` and `{[false]}` is regular and contains `[false, true]`.
* The cyclic shifts of `{[true, false]}` form a regular language containing `[false, true]`.
* The generic statements are instantiated.
-/

@[expose] public section

namespace Cslib.Language.RegularShuffleTests

example : IsShuffle [true] [false] [true, false] := .left _ (.right _ .nil)

example : IsShuffle [true] [false] [false, true] := .right _ (.left _ .nil)

example : ¬ IsShuffle [true] [false] [true, true] := by
  intro h
  rcases isShuffle_cons_iff.1 h with ⟨u, hu, h'⟩ | ⟨v, hv, _⟩
  · cases hu
    rcases isShuffle_cons_iff.1 h' with ⟨_, hu', _⟩ | ⟨_, hv', _⟩
    · cases hu'
    · cases hv'
  · cases hv

example : (shuffle ({[true]} : Language Bool) {[false]}).IsRegular :=
  IsRegular.shuffle (IsRegular.singleton_word _) (IsRegular.singleton_word _)

example : [false, true] ∈ shuffle ({[true]} : Language Bool) {[false]} :=
  mem_shuffle.2 ⟨[true], rfl, [false], rfl, .right _ (.left _ .nil)⟩

example : (cyclicShift ({[true, false]} : Language Bool)).IsRegular :=
  IsRegular.cyclicShift (IsRegular.singleton_word _)

example : [false, true] ∈ cyclicShift ({[true, false]} : Language Bool) :=
  mem_cyclicShift.2 ⟨[true], [false], rfl, rfl⟩

example : [true] ∈ RegularShuffle.fromTo (⟨fun _ b => b, false, {true}⟩ : DFA Bool Bool) false
    {true} :=
  RegularShuffle.mem_fromTo _ |>.2 rfl

example {T : Type} {L M : Language T} (hL : L.IsRegular) (hM : M.IsRegular) :
    (shuffle L M).IsRegular ∧ (cyclicShift L).IsRegular :=
  ⟨IsRegular.shuffle hL hM, IsRegular.cyclicShift hL⟩

end Cslib.Language.RegularShuffleTests
