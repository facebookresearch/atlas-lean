/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.BinaryHeap
meta import CSLibExt.Algorithms.Lean.DataStructures.BinaryHeap

/-!
# Tests for the binary min-heap API

These client examples exercise the executable operations and their public correctness API.
-/

public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.BinaryHeapTests

example {α : Type} [LinearOrder α] (heap : MinHeap α) (value : α) :
    HeapOrdered (heap.push value).data :=
  heap.push_ordered value

example {α : Type} [LinearOrder α] (heap : MinHeap α) (value : α) :
    (heap.push value).elements = value ::ₘ heap.elements :=
  heap.elements_push value

example {α : Type} [LinearOrder α] (heap : MinHeap α) (value : α) :
    Multiset.count value (heap.push value).elements =
      Multiset.count value heap.elements + 1 :=
  heap.count_push_self value

example {α : Type} [LinearOrder α] {heap : MinHeap α} {value : α}
    {rest : MinHeap α} (result : heap.extractMin = some (value, rest)) :
    value ::ₘ rest.elements = heap.elements :=
  heap.extractMin_cons_elements result

example {α : Type} [LinearOrder α] {heap : MinHeap α} {value : α}
    {rest : MinHeap α} (result : heap.extractMin = some (value, rest)) :
    HeapOrdered rest.data :=
  heap.extractMin_ordered result

/-- Project an extraction result to its returned value and backing array. -/
def extractedData (heap : MinHeap Nat) : Option (Nat × Array Nat) :=
  heap.extractMin.map fun result => (result.1, result.2.data)

example : (MinHeap.empty : MinHeap Nat).data = #[] := by
  rfl

example : (MinHeap.empty : MinHeap Nat).min? = none := by
  rfl

example : extractedData (MinHeap.empty : MinHeap Nat) = none := by
  rfl

private def singleton : MinHeap Nat := MinHeap.empty.push 4

example : singleton.data = #[4] := by
  simp [singleton, MinHeap.push, MinHeap.empty, siftUp]

example : singleton.min? = some 4 := by
  simp [singleton, MinHeap.min?, MinHeap.push, MinHeap.empty, siftUp]

example : extractedData singleton = some (4, #[]) := by
  simp [extractedData, singleton, MinHeap.extractMin, MinHeap.extractTail, MinHeap.push,
    MinHeap.empty, siftUp]

private def duplicates : MinHeap Nat :=
  MinHeap.empty.push 3 |>.push 1 |>.push 1 |>.push 2

example : duplicates.data = #[1, 2, 1, 3] := by
  simp [duplicates, MinHeap.push, MinHeap.empty, siftUp, heapParent]

example : Multiset.count 1 duplicates.elements = 2 := by
  simp [duplicates, MinHeap.elements, MinHeap.push, MinHeap.empty, siftUp, heapParent]

example : Multiset.count 2 duplicates.elements = 1 := by
  simp [duplicates, MinHeap.elements, MinHeap.push, MinHeap.empty, siftUp, heapParent]

example : extractedData duplicates = some (1, #[1, 2, 3]) := by
  simp [extractedData, duplicates, MinHeap.extractMin, MinHeap.extractTail, MinHeap.push,
    MinHeap.empty, siftUp, siftDown, smallerChild, moveLastToRoot, heapParent, heapLeft,
    heapRight]

example : siftUp #[1, 2, 3, 4] 3 = #[1, 2, 3, 4] := by
  simp [siftUp, heapParent]

example : siftDown #[1, 2, 3, 4, 5] 0 = #[1, 2, 3, 4, 5] := by
  simp [siftDown, smallerChild, heapLeft, heapRight]

example : siftUp #[1, 4, 2, 7, 8, 9, 0] 6 = #[0, 4, 1, 7, 8, 9, 2] := by
  simp [siftUp, heapParent]

example : siftDown #[9, 2, 3, 4, 5, 6, 7] 0 = #[2, 4, 3, 9, 5, 6, 7] := by
  simp [siftDown, smallerChild, heapLeft, heapRight]

private def unrelatedUp : Array Nat := siftUp #[1, 9, 2, 0, 8, 9, 0] 6

example : unrelatedUp = #[0, 9, 1, 0, 8, 9, 2] := by
  simp [unrelatedUp, siftUp, heapParent]

example : unrelatedUp[3]! < unrelatedUp[1]! := by
  simp [unrelatedUp, siftUp, heapParent]

private def unrelatedDown : Array Nat := siftDown #[9, 2, 3, 4, 5, 0, 7] 0

example : unrelatedDown = #[2, 4, 3, 9, 5, 0, 7] := by
  simp [unrelatedDown, siftDown, smallerChild, heapLeft, heapRight]

example : unrelatedDown[5]! < unrelatedDown[2]! := by
  simp [unrelatedDown, siftDown, smallerChild, heapLeft, heapRight]

end Cslib.Algorithms.Lean.BinaryHeapTests

namespace Cslib.Algorithms.Lean.BinaryHeapTests

-- Runtime clients; these IO checks are not proof certificates.
private meta def checkExtraction
    (extract : MinHeap Nat → Option (Nat × MinHeap Nat)) (input : List Nat) : IO Unit := do
  let heap := input.foldl MinHeap.push MinHeap.empty
  let built := heap.data.toList
  unless (input ++ built).all (fun v => input.count v == built.count v) do
    throw (IO.userError s!"heap construction input={input} built={built}")
  let result := extract heap
  unless result.isNone == input.isEmpty do
    throw (IO.userError s!"heap presence input={input} none={result.isNone}")
  match result with
  | none => pure ()
  | some (x, rest) =>
    let output := x :: rest.data.toList
    -- Both supports matter: a fabricated returned value must also be counted.
    unless (input ++ output).all (fun v => input.count v == output.count v) do
      throw (IO.userError s!"heap partition input={input} output={output}")
    unless input.all (fun v => x ≤ v) do
      throw (IO.userError s!"heap minimum input={input} returned={x}")

private meta def heapInputs : Plausible.Rand (List (List Nat)) :=
  (List.range 1000).mapM fun _ => do
    let n ← Plausible.Random.randBound Nat 0 12 (by decide)
    (List.range n.val).mapM fun _ => do
      return (← Plausible.Random.randBound Nat 0 7 (by decide)).val

private meta def runExtractionTests : IO Unit := do
  let inputs := (heapInputs.run ⟨mkStdGen 2026110401⟩).1
  let fixed := [[], [4], [3, 1, 1, 2], (List.range 12).map (· % 8)]
  let lengths := (List.range 13).map fun n => (inputs.filter (·.length == n)).length
  let values := (List.range 8).map fun n => inputs.flatten.count n
  unless inputs.length == 1000 && lengths.all (· > 0) && values.all (· > 0) do
    throw (IO.userError "heap generator coverage")
  for input in fixed ++ inputs do
    unless input.length ≤ 12 && input.all (· ≤ 7) do
      throw (IO.userError "heap generator bounds")
    checkExtraction MinHeap.extractMin input
  let duplicates := (inputs.filter fun xs => xs.any (fun x => xs.count x > 1)).length
  unless duplicates > 0 do throw (IO.userError "heap duplicate coverage")
  IO.println s!"S2 heap seed=2026110401 generated={inputs.length} fixed={fixed.length}"
  IO.println s!"S2 heap checks={inputs.length + fixed.length} retries=0 discards=0"
  IO.println s!"S2 heap lengths={lengths} values={values} duplicateLists={duplicates}"

#eval runExtractionTests

end Cslib.Algorithms.Lean.BinaryHeapTests
