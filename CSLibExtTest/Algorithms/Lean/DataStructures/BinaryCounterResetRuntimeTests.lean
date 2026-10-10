/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public meta import CSLibExt.Algorithms.Lean.DataStructures.BinaryCounter

set_option autoImplicit false

open Cslib.Algorithms.Lean.BinaryCounter

private def width0 : Vector Bool 0 :=
  ⟨#[], by decide⟩

private def width1False : Vector Bool 1 :=
  ⟨#[false], by decide⟩

private def width1True : Vector Bool 1 :=
  ⟨#[true], by decide⟩

private def width4False : Vector Bool 4 :=
  ⟨#[false, false, false, false], by decide⟩

private meta def width4True : Vector Bool 4 :=
  ⟨#[true, true, true, true], by decide⟩

private meta def width4Mixed : Vector Bool 4 :=
  ⟨#[true, false, true, false], by decide⟩

private meta def savedIncrement : Vector Bool 4 :=
  (increment width4Mixed).ret

private meta def savedIncrementWrap : Vector Bool 4 :=
  (increment width4True).ret

private meta def savedRun : Vector Bool 4 :=
  (run width4Mixed 5).ret

private meta def savedRunWrap : Vector Bool 4 :=
  (run width4True 1).ret

-- Preserve the seven populated runtime rows from the failed combined client.
#eval (reset width0).ret.toList
#eval (reset width1True).time
#eval (reset width4Mixed).ret.toList
#eval (reset width4Mixed).time
#eval (reset (Vector.replicate 65 true)).time
#eval (reset savedIncrement).time
#eval (reset savedRun).time

-- Exact executable expectations belong in this public-meta-only client.
#guard (reset width0).ret.toList = []
#guard (reset width0).time = 0
#guard (reset width1False).ret.toList = [false]
#guard (reset width1False).time = 0
#guard (reset width1True).ret.toList = [false]
#guard (reset width1True).time = 1
#guard (reset width4False).ret.toList = [false, false, false, false]
#guard (reset width4False).time = 0
#guard (reset width4True).ret.toList = [false, false, false, false]
#guard (reset width4True).time = 4
#guard (reset width4Mixed).ret.toList = [false, false, false, false]
#guard (reset width4Mixed).time = 2
#guard (reset (reset width4Mixed).ret).ret = (reset width4Mixed).ret
#guard (reset (reset width4Mixed).ret).time = 0
#guard (reset (Vector.replicate 65 false)).ret.toList = List.replicate 65 false
#guard (reset (Vector.replicate 65 false)).time = 0
#guard (reset (Vector.replicate 65 true)).ret.toList = List.replicate 65 false
#guard (reset (Vector.replicate 65 true)).time = 65
#guard savedIncrement.toList = [false, true, true, false]
#guard (reset savedIncrement).ret.toList = [false, false, false, false]
#guard (reset savedIncrement).time = 2
#guard savedIncrementWrap.toList = [false, false, false, false]
#guard (reset savedIncrementWrap).ret.toList = [false, false, false, false]
#guard (reset savedIncrementWrap).time = 0
#guard savedRun.toList = [false, true, false, true]
#guard (reset savedRun).ret.toList = [false, false, false, false]
#guard (reset savedRun).time = 2
#guard savedRunWrap.toList = [false, false, false, false]
#guard (reset savedRunWrap).ret.toList = [false, false, false, false]
#guard (reset savedRunWrap).time = 0
#guard (reset width4Mixed).time ≠ 3
#guard (reset width4Mixed).ret.toList ≠ [true, false, false, false]
