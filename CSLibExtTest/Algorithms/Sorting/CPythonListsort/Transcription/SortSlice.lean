/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import CSLibExt.Algorithms.Sorting.CPythonListsort.Transcription.SortSlice

/-! # Fixed-input `sortslice` movement regressions -/

namespace CPythonListsort.SortSlice

private def overlapExample : SortSlice Nat Nat :=
  { entries :=
      #[{ key := 1, value := some 10 },
        { key := 2, value := some 20 },
        { key := 3, value := some 30 },
        { key := 4, value := some 40 }] }

/-- Equal contents do not collapse explicit distinct-backing provenance. -/
example :
    memcpy? 4 overlapExample (.distinctBacking overlapExample) 0 0 =
      some overlapExample := by
  decide

/-- A positive exact self-copy overlaps and is therefore not a `memcpy`. -/
example : memcpy? 1 overlapExample .sameBacking 0 0 = none := by
  decide

/-- The rejection is range-based, not limited to the one-cell boundary. -/
example : memcpy? 2 overlapExample .sameBacking 1 1 = none := by
  decide

/-- Same-backing ranges may meet at the source-to-destination endpoint. -/
example :
    memcpy? 2 overlapExample .sameBacking 2 0 =
      some
        { entries :=
            #[{ key := 1, value := some 10 },
              { key := 2, value := some 20 },
              { key := 1, value := some 10 },
              { key := 2, value := some 20 }] } := by
  decide

/-- Same-backing ranges may also meet in the opposite order. -/
example :
    memcpy? 2 overlapExample .sameBacking 0 2 =
      some
        { entries :=
            #[{ key := 3, value := some 30 },
              { key := 4, value := some 40 },
              { key := 3, value := some 30 },
              { key := 4, value := some 40 }] } := by
  decide

/-- An empty copy admits equal one-past cursors on a shared backing. -/
example : memcpy? 0 overlapExample .sameBacking 4 4 = some overlapExample := by
  decide

/-- A rightward overlapping move retains the unread entries and their payloads. -/
example :
    overlapExample.memmove? 1 0 3 =
      some
        { entries :=
            #[{ key := 1, value := some 10 },
              { key := 1, value := some 10 },
              { key := 2, value := some 20 },
              { key := 3, value := some 30 }] } := by
  decide

/-- Equal contents do not turn explicit distinct provenance into aliasing. -/
example :
    memmoveFrom? overlapExample (.distinctBacking overlapExample) 0 0 4 =
      some overlapExample := by
  decide

/-- The general same-backing API retains backward-safe rightward overlap. -/
example :
    memmoveFrom? overlapExample .sameBacking 1 0 3 =
      some
        { entries :=
            #[{ key := 1, value := some 10 },
              { key := 1, value := some 10 },
              { key := 2, value := some 20 },
              { key := 3, value := some 30 }] } := by
  decide

end CPythonListsort.SortSlice
