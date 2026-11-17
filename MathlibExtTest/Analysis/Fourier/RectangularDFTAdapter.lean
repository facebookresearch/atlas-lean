/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Fourier.RectangularDFTAdapter

@[expose] public section

open MathlibExt.Analysis.Fourier.RectangularDFTAdapter

namespace MathlibExtTest.Analysis.Fourier.RectangularDFTAdapter

/-- The unit impulse at the origin has flat spectrum `1`. -/
example : rowColumnDFT (fun p : ZMod 2 × ZMod 3 => if p = (0, 0) then (1 : ℂ) else 0)
    = fun _ => 1 :=
  rowColumnDFT_impulse_origin

end MathlibExtTest.Analysis.Fourier.RectangularDFTAdapter
