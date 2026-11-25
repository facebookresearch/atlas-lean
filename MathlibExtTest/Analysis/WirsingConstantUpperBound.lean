/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.WirsingConstantUpperBound

open MathlibExt.Analysis.WirsingConstant
open MathlibExt.Analysis.WirsingConstantWanted

-- The bound excludes 1/3 in the holomorphic model.
example : wirsingConstant < 1 / 3 :=
  mayerRoepstorffUpperBound_wanted.trans_lt (by norm_num)
