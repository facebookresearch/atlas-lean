/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Words.RegularSequence

namespace MetaMathlibExt

example : IsKRegularSequence 2 (fun _ => (5 : ℤ)) := isKRegularSequence_const le_rfl 5

example : ¬ IsKRegularSequence 1 (fun _ => (0 : ℤ)) := fun h => by
  have := h.two_le
  omega

end MetaMathlibExt
