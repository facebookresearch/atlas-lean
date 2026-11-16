/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Crypto.Feistel

@[expose] public section

/-- With the zero round function, a round swaps the halves. -/
example : feistelRound (n := 1) (fun _ => fun _ => false)
    (fun _ => true, fun _ => false) = (fun _ => false, fun _ => true) := rfl

end
