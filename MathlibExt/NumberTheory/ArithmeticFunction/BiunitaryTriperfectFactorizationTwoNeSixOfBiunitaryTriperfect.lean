/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.ArithmeticFunction.BiunitaryTriperfect

/-!
# Excluding exponent six at two for biunitary triperfect numbers divisible by 27

A positive biunitary triperfect number divisible by 27 cannot have exponent six at two. The
theorem `factorization_two_ne_six_of_biunitaryTriperfect` is proved in
`MathlibExt.NumberTheory.ArithmeticFunction.BiunitaryTriperfect`, next to the biunitary
divisor-sum lemmas it uses; this module re-exports it.

Source: Tomohiro Yamada, *Determining all Biunitary Triperfect Numbers of a Certain Form*,
Journal of Integer Sequences 28 (2025), Article 25.4.5, Lemma 11.
-/
