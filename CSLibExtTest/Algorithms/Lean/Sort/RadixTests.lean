/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public meta import CSLibExt.Algorithms.Lean.Sort.Radix

@[expose] public section

namespace Cslib.Algorithms.Lean.TimeM

universe u

private structure DigitRecord (b d : Nat) where
  digits : Vector (Fin b) d
  tag : Nat
deriving BEq, DecidableEq

private def recordDigits {b d : Nat} (x : DigitRecord b d) : Vector (Fin b) d := x.digits

#guard
  (radixSort recordDigits (#[] : Array (DigitRecord 2 2)) (by decide)).ret == #[]

#guard
  (radixSort recordDigits (#[] : Array (DigitRecord 2 2)) (by decide)).time == 12

#guard
  (radixSort recordDigits
    (#[DigitRecord.mk #v[] 0, DigitRecord.mk #v[] 1] : Array (DigitRecord 2 0))
    (by decide)).ret ==
    (#[DigitRecord.mk #v[] 0, DigitRecord.mk #v[] 1] : Array (DigitRecord 2 0))

#guard
  (radixSort recordDigits
    #[DigitRecord.mk #v[(1 : Fin 2)] 0, DigitRecord.mk #v[(0 : Fin 2)] 1]
    (by decide)).ret ==
    #[DigitRecord.mk #v[(0 : Fin 2)] 1, DigitRecord.mk #v[(1 : Fin 2)] 0]

#guard
  (radixSort recordDigits
    #[DigitRecord.mk #v[(1 : Fin 2), (1 : Fin 2)] 0,
      DigitRecord.mk #v[(0 : Fin 2), (1 : Fin 2)] 1,
      DigitRecord.mk #v[(1 : Fin 2), (0 : Fin 2)] 2,
      DigitRecord.mk #v[(0 : Fin 2), (0 : Fin 2)] 3]
    (by decide)).ret ==
    #[DigitRecord.mk #v[(0 : Fin 2), (0 : Fin 2)] 3,
      DigitRecord.mk #v[(0 : Fin 2), (1 : Fin 2)] 1,
      DigitRecord.mk #v[(1 : Fin 2), (0 : Fin 2)] 2,
      DigitRecord.mk #v[(1 : Fin 2), (1 : Fin 2)] 0]

#guard
  (radixSort recordDigits
    #[DigitRecord.mk #v[(0 : Fin 3), (2 : Fin 3)] 0,
      DigitRecord.mk #v[(0 : Fin 3), (0 : Fin 3)] 1,
      DigitRecord.mk #v[(0 : Fin 3), (2 : Fin 3)] 2,
      DigitRecord.mk #v[(0 : Fin 3), (1 : Fin 3)] 3]
    (by decide)).ret ==
    #[DigitRecord.mk #v[(0 : Fin 3), (0 : Fin 3)] 1,
      DigitRecord.mk #v[(0 : Fin 3), (1 : Fin 3)] 3,
      DigitRecord.mk #v[(0 : Fin 3), (2 : Fin 3)] 0,
      DigitRecord.mk #v[(0 : Fin 3), (2 : Fin 3)] 2]

#guard
  (radixSort recordDigits
    #[DigitRecord.mk #v[(0 : Fin 3), (0 : Fin 3)] 0,
      DigitRecord.mk #v[(0 : Fin 3), (1 : Fin 3)] 1,
      DigitRecord.mk #v[(2 : Fin 3), (2 : Fin 3)] 2]
    (by decide)).ret ==
    #[DigitRecord.mk #v[(0 : Fin 3), (0 : Fin 3)] 0,
      DigitRecord.mk #v[(0 : Fin 3), (1 : Fin 3)] 1,
      DigitRecord.mk #v[(2 : Fin 3), (2 : Fin 3)] 2]

#guard
  (radixSort recordDigits
    #[DigitRecord.mk #v[(2 : Fin 3), (2 : Fin 3)] 2,
      DigitRecord.mk #v[(0 : Fin 3), (1 : Fin 3)] 1,
      DigitRecord.mk #v[(0 : Fin 3), (0 : Fin 3)] 0]
    (by decide)).ret ==
    #[DigitRecord.mk #v[(0 : Fin 3), (0 : Fin 3)] 0,
      DigitRecord.mk #v[(0 : Fin 3), (1 : Fin 3)] 1,
      DigitRecord.mk #v[(2 : Fin 3), (2 : Fin 3)] 2]

#guard
  (radixSort recordDigits
    #[DigitRecord.mk #v[(2 : Fin 3), (2 : Fin 3)] 0,
      DigitRecord.mk #v[(2 : Fin 3), (2 : Fin 3)] 1]
    (by decide)).ret ==
    #[DigitRecord.mk #v[(2 : Fin 3), (2 : Fin 3)] 0,
      DigitRecord.mk #v[(2 : Fin 3), (2 : Fin 3)] 1]

#guard
  (radixSort recordDigits
    #[DigitRecord.mk #v[(1 : Fin 2), (1 : Fin 2)] 0,
      DigitRecord.mk #v[(0 : Fin 2), (0 : Fin 2)] 1]
    (by decide)).time == 40

/- error: Tactic `decide` proved that the proposition
  2 ≤ 0
is false -/
#guard_msgs (error, substring := true) in
#check radixSort (b := 0) (d := 0)
  (fun _ : Fin 0 => (#v[] : Vector (Fin 0) 0)) #[] (by decide)

/- error: 2 ≤ 0 → -/
#guard_msgs (error, substring := true) in
#check (radixSort (b := 0) (d := 0)
  (fun _ : Fin 0 => (#v[] : Vector (Fin 0) 0)) #[] : TimeM Nat (Array (Fin 0)))

/- error: Tactic `decide` proved that the proposition
  2 ≤ 1
is false -/
#guard_msgs (error, substring := true) in
#check radixSort (b := 1) (d := 0)
  (fun _ : Nat => (#v[] : Vector (Fin 1) 0)) #[] (by decide)

/- error: 2 ≤ 1 → -/
#guard_msgs (error, substring := true) in
#check (radixSort (b := 1) (d := 0)
  (fun _ : Nat => (#v[] : Vector (Fin 1) 0)) #[] : TimeM Nat (Array Nat))

example {α : Type u} {b d : Nat} (digits : α → Vector (Fin b) d)
    (input : Array α) (hb : 2 ≤ b) :
    List.Perm (radixSort digits input hb).ret.toList input.toList :=
  (radixSort_correct digits input hb).2.1

example {α : Type u} {b d : Nat} (digits : α → Vector (Fin b) d)
    (input : Array α) (hb : 2 ≤ b) :
    (radixSort digits input hb).time ≤ d * (7 * input.size + 3 * b) :=
  radixSort_time digits input hb

end Cslib.Algorithms.Lean.TimeM
