/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Foundations.Semantics.PagedAddressTranslation

namespace CSLibExtTest.Foundations.Semantics.PagedAddressTranslation

open Cslib.Semantics.PagedAddressTranslation

private def readOnly : Access → Bool
  | .read => true
  | _ => false

private def first : Mapping := ⟨3, readOnly⟩
private def second : Mapping := ⟨7, readOnly⟩

private def table : PageTable where
  base := 40
  entryBytes := 3
  entryBytes_pos := by decide
  entryAt := fun
    | 40 => ⟨true, true, first⟩
    | 43 => ⟨true, true, second⟩
    | 49 => ⟨true, false, first⟩
    | _ => ⟨false, false, first⟩

private def empty : Cache := fun _ => none
private def filled : Cache := (translate table empty 2 .read 1).2

-- The last byte of page zero and the first byte of page one use adjacent table slots
-- and different frames. The second translation has zero offset.
example : (vpn 2 3, offset 2 3, vpn 2 4, offset 2 4) = (0, 3, 1, 0) := rfl
example : table.entryAddress 1 = 43 := rfl
example : (translate table empty 2 .read 3).1 = .ok 15 := rfl
example : (translate table empty 2 .read 4).1 = .ok 28 := rfl

-- A successful miss inserts the frame and permissions only for the requested page.
example : (translate table empty 2 .read 1).1 = .ok 13 := rfl
example : filled 0 = some first := rfl
example : filled 1 = none := rfl

-- Every fault preserves the whole cache, including the already cached page. Invalid
-- takes precedence when all three checks fail; permission precedes nonresidence.
example : translate table filled 2 .write 8 = (.error .invalid, filled) := rfl
example : translate table filled 2 .write 12 = (.error .protection, filled) := rfl
example : translate table filled 2 .read 12 = (.error .nonresident, filled) := rfl

-- A permitted hit uses the new offset; a denied hit still checks the cached permissions.
example : translate table filled 2 .read 3 = (.ok 15, filled) := rfl
example : translate table filled 2 .write 2 = (.error .protection, filled) := rfl

end CSLibExtTest.Foundations.Semantics.PagedAddressTranslation
