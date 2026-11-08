/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Matrix.Freivalds.Amplification
public import CSLibExt.Algorithms.Lean.Matrix.Freivalds.Sharpness

/-!
# Binary Freivalds matrix-product verification

The actual charged trial computes three materialized matrix-vector products
over `ZMod 2`. Its ideal uniform seed law has one-sided error at most one half.
Uniform complete histories give the repeated executor error at most `2⁻ᵏ`.
The same executions count exactly `3n²` and `3kn²` scalar multiplications and
additions. Random-bit acquisition and other operations are outside these counters.

MIT 6.046J Spring 2015 Lecture 6, printed page 2, supplies the binary-seed trial.

This implementation is an intentional strict GF(2) specialization: the cited lecture chooses a
random binary vector for matrices over a general coefficient domain and does not restrict `A`,
`B`, `C` or their arithmetic to `ZMod 2`, whereas here the matrices and all arithmetic are over
`ZMod 2`. The specialization loses scope (for example, integer `[1] * [1]` and `[3]` are unequal
in the source setting but become equal after reduction modulo 2).
Independent repetition is the explicitly documented campaign extension.

Retained Lean was authored by Codex at Adam Kiezun's explicit selection.
-/
