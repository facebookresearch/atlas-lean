/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.LinearRecurrence

/-!
# The annihilator of a geometric sequence

The polynomial `X - C c` annihilates the geometric sequence with ratio `c`, including `c = 0`.
-/

namespace MetaMathlibExt

open Polynomial

/-- **The operator $E - c$ annihilates the powers of $c$.** Let $K$ be a field, $c \in K$, and let
$E$ be the translation operator $E(G_s) = G_{s+1}$ on sequences $G \colon \mathbb{N} \to K$. Then
the operator $E - c$, that is, $p(E)$ for the polynomial $p = X - c \in K[X]$, annihilates the
sequence $s \mapsto c^s$.

Source: Emily J. Evans and Russell Jay Hendel, *Recursions and Characteristic Polynomials of the
Rows of the Circuit Array*, Fibonacci Quarterly 62 (2024), Article 62-4/hendel08232024rev2,
Lemma 3.7 (`fq-2024-hendel08232024rev2-lem-3.7`), part (i). -/
public theorem annihilatesSeq_X_sub_C_pow {K : Type*} [Field K] (c : K) :
    AnnihilatesSeq (X - C c) (fun s => c ^ s) := by
  intro s
  change ((X - C c).sum fun i a => a * c ^ (s + i)) = 0
  simp only [pow_add, mul_left_comm _ (c ^ s)]
  rw [Polynomial.sum, ← Finset.mul_sum]
  change c ^ s * ((X - C c).sum fun i a => a * c ^ i) = 0
  rw [← Polynomial.eval_eq_sum]
  simp only [eval_sub, eval_X, eval_C, sub_self, mul_zero]

end MetaMathlibExt
