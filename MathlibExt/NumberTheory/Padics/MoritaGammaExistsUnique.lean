/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.Padics.MoritaGammaPadic

/-!
# Existence of Morita's p-adic gamma function (compatibility module)

The construction of Morita's `p`-adic gamma function now lives in
`MathlibExt.NumberTheory.Padics.MoritaGammaPadic`, which proves
`MetaMathlibExt.existsUnique_isMoritaPadicGamma` for every prime `p`. This module is kept so that
existing imports of `MathlibExt.NumberTheory.Padics.MoritaGammaExistsUnique` keep compiling; it
re-exports that module, including the deprecated odd-prime statement
`MetaMathlibExt.existsUnique_moritaPadicGamma`.
-/
