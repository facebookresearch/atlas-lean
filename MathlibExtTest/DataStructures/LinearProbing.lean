/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.DataStructures.LinearProbing

@[expose] public section

/-- Lookup finds a key sitting at its home slot. -/
example : probeLookup 8 (fun _ => 0) 5 1 0 (fun _ => some 5) = true := rfl

end
