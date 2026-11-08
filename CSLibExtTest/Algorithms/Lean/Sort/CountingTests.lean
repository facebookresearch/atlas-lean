/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public meta import CSLibExt.Algorithms.Lean.Sort.Counting

@[expose] public section

namespace Cslib.Algorithms.Lean.TimeM

universe u

private structure Tagged (k : Nat) where
  key : Fin k
  tag : Nat
deriving BEq, DecidableEq

private def taggedKey {k : Nat} (x : Tagged k) : Fin k := x.key

example : (countingSort (fun x : Fin 0 => x) #[]).ret = #[] := by
  decide

example : (countingSort (fun x : Fin 0 => x) #[]).time = 0 := by
  decide

example : (countingSort (fun x : Fin 3 => x) #[]).ret = #[] := by
  decide

example : (countingSort (fun x : Fin 3 => x) #[]).time = 9 := by
  decide

#guard
  (countingSort taggedKey
    #[Tagged.mk (0 : Fin 1) 10, Tagged.mk 0 11, Tagged.mk 0 12]).ret ==
    #[Tagged.mk (0 : Fin 1) 10, Tagged.mk 0 11, Tagged.mk 0 12]

#guard
  (countingSort taggedKey #[Tagged.mk (0 : Fin 4) 10]).ret ==
    #[Tagged.mk (0 : Fin 4) 10]

#guard
  (countingSort taggedKey #[Tagged.mk (3 : Fin 4) 10]).ret ==
    #[Tagged.mk (3 : Fin 4) 10]

#guard
  (countingSort taggedKey
    #[Tagged.mk (0 : Fin 5) 0, Tagged.mk 3 1, Tagged.mk 3 2]).ret ==
    #[Tagged.mk (0 : Fin 5) 0, Tagged.mk 3 1, Tagged.mk 3 2]

#guard
  (countingSort taggedKey
    #[Tagged.mk (0 : Fin 4) 0, Tagged.mk 1 1, Tagged.mk 2 2, Tagged.mk 3 3]).ret ==
    #[Tagged.mk (0 : Fin 4) 0, Tagged.mk 1 1, Tagged.mk 2 2, Tagged.mk 3 3]

#guard
  (countingSort taggedKey
    #[Tagged.mk (3 : Fin 4) 3, Tagged.mk 2 2, Tagged.mk 1 1, Tagged.mk 0 0]).ret ==
    #[Tagged.mk (0 : Fin 4) 0, Tagged.mk 1 1, Tagged.mk 2 2, Tagged.mk 3 3]

#guard
  (countingSort taggedKey
    #[Tagged.mk (2 : Fin 3) 0, Tagged.mk 2 1, Tagged.mk 2 2]).ret ==
    #[Tagged.mk (2 : Fin 3) 0, Tagged.mk 2 1, Tagged.mk 2 2]

#guard
  (countingSort taggedKey
    #[Tagged.mk (2 : Fin 3) 0, Tagged.mk 0 1, Tagged.mk 2 2,
      Tagged.mk 1 3, Tagged.mk 2 4]).ret ==
    #[Tagged.mk (0 : Fin 3) 1, Tagged.mk 1 3, Tagged.mk 2 0,
      Tagged.mk 2 2, Tagged.mk 2 4]

example :
    (countingSort taggedKey
      #[Tagged.mk (2 : Fin 3) 0, Tagged.mk 0 1, Tagged.mk 2 2,
        Tagged.mk 1 3, Tagged.mk 2 4]).time = 44 := by
  decide

example {α : Type u} {k : Nat} (key : α → Fin k) (input : Array α) :
    List.Perm (countingSort key input).ret.toList input.toList :=
  (countingSort_correct key input).2.1

example {α : Type u} {k : Nat} (key : α → Fin k) (input : Array α) :
    (countingSort key input).time ≤ 7 * input.size + 3 * k :=
  countingSort_time key input

end Cslib.Algorithms.Lean.TimeM
