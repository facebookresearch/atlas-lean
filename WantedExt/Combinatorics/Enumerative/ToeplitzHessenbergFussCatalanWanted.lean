/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Toeplitz-Hessenberg determinants with Fuss-Catalan entries

Statements from Taras Goy and Mark Shattuck, *Determinants of Toeplitz-Hessenberg Matrices with
Fuss-Catalan Entries*, Journal of Integer Sequences 29 (2026), Article 26.1.2.

`toeplitzHessenbergDet a n` is the determinant of the `n × n` Toeplitz-Hessenberg matrix with
`a 0` on the superdiagonal and `a 1, …, a n` down the first column. The paper's
`D_±(a_1, …, a_n)` is `toeplitzHessenbergDet (fun i => if i = 0 then ±1 else a i) n`.
The Fuss-Catalan (Raney) number `A_n(p, r)` is `(generalizedFussCatalanNumber p n r : ℚ)`
(MathlibExt), so `C_n = A_n(2, 1)`,
`K_n = A_n(2, 3) = C_{n+2} - C_{n+1}`, `H_n = A_n(3, 1)`, `J_n = A_n(3, 2)`. The Catalan generating
function `C(x)` is `PowerSeries.mk fun n => (catalan n : ℚ)`. Generating-function statements are
written multiplicatively.
-/
module

import Batteries.Util.ProofWanted
public import Mathlib.Combinatorics.Enumerative.Catalan.Basic
public import Mathlib.RingTheory.Binomial
public import Mathlib.RingTheory.PowerSeries.Basic
public import MathlibExt.Combinatorics.Enumerative.DyckPeakDescents
public import MathlibExt.Combinatorics.Enumerative.EvenNoncrossingDyckDescents
public import MathlibExt.Combinatorics.Enumerative.ToeplitzHessenbergDetCatalan
public import MathlibExt.Combinatorics.Enumerative.ToeplitzHessenbergDetFussCatalan
public import MathlibExt.Combinatorics.Enumerative.ToeplitzHessenbergDetFussCatalanSpecial
public import MathlibExt.Combinatorics.Enumerative.ToeplitzHessenbergDetGenFun
public import MathlibExt.Combinatorics.Enumerative.TrudiFussCatalan
public import MathlibExt.Combinatorics.NoncrossingPartition.Basic
public import MathlibExt.LinearAlgebra.Matrix.TrudiBrioschiDeterminant
public import MathlibExt.NumberTheory.GeneralizedFussCatalanNumbersFMNK

namespace MetaMathlibExt

@[expose] public section

/-- **Small generalized Fuss–Catalan numbers.** For the generalized Fuss–Catalan numbers
$A_n(p, r) = \frac{r}{pn + r} \binom{pn + r}{n}$, one has $A_3(2, 1) = 5$, $A_2(2, 3) = 9$,
$A_3(3, 1) = 12$ and $A_2(3, 2) = 7$.

With $C_n$ the $n$-th Catalan number, $A_3(2, 1) = C_3$ and $A_2(2, 3) = C_4 - C_3$.

Source: Taras Goy and Mark Shattuck, *Determinants of Toeplitz-Hessenberg Matrices with
Fuss-Catalan Entries*, Journal of Integer Sequences 29 (2026), Article 26.1.2, Sections 1-2
(`C_n = A_n(2, 1)`, `K_n = A_n(2, 3)`, `H_n = A_n(3, 1)`, `J_n = A_n(3, 2)`). -/
theorem toeplitzHessenberg_fussCatalan_examples :
    generalizedFussCatalanNumber 2 3 1 = 5 ∧ generalizedFussCatalanNumber 2 2 3 = 9 ∧
      generalizedFussCatalanNumber 3 3 1 = 12 ∧ generalizedFussCatalanNumber 3 2 2 = 7 := by
  decide

end

end MetaMathlibExt
