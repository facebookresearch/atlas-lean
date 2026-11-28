/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Computability.Complexity.PolynomialEncoding.StreamScan

/-! Regression tests for framed scans on empty, nonempty, and truncated payloads. -/

open MetaMathlibExt.BitstringEncoding
open Cslib.Complexity.PolynomialEncoding.StreamScan

-- Each complete frame is marked, including an empty payload.
example : marks [true] (([[], [false, true]].map delimit).flatten) = [true, true] := by
  rw [marks_frames]
  rfl

-- The empty frame supplies `none`; the next frame supplies its final payload bit.
private def close : Option Bool → List Bool
  | none => [true]
  | some b => [b]

example :
    blocks [false] (fun b => [b]) close (delimit [] ++ delimit [true, false] ++ []) =
      [false, true, false, true, false, false] := by
  rw [List.append_assoc, blocks_frame, blocks_frame, blocks_nil]
  rfl

example : listRejectSuffix (delimit [] ++ delimit [true]) = [] := by decide

-- The last `true` asks for a payload bit that is not present.
example : listRejectSuffix (delimit [false] ++ [true]) = [true] := by decide
