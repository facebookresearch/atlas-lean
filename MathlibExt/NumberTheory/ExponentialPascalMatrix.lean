/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Matrix.Basic
public import Mathlib.RingTheory.PowerSeries.Exp

/-!
# Exponential Pascal-type matrices

The source identifies a family of exponential Riordan arrays represented by
`[e^t, t + r * t^2 / 2]`.  This file records both the generating-function pair and the
associated matrix.  Its `(n, k)` entry is

`n! / k! * [t^n] e^t * (t + r * t^2 / 2)^k`.

The parameter `r = 1` gives the Pascal-like matrix OEIS A100862, while `r = 2` gives the
example `[e^t, t + t^2]` from the source.

Source: Paul Barry, *Constructing Exponential Riordan Arrays from Their A and Z Sequences*,
<https://cs.uwaterloo.ca/journals/JIS/VOL17/Barry2/barry281.tex>.

JIS concept: `jis_sem_26c56e556549984950a493f3`.
-/

namespace MetaMathlibExt

@[expose] public section

variable (R : Type*) [CommRing R] [Algebra ℚ R]

/-- **Second series of the exponential Pascal-type pair.** Let $R$ be a commutative ring
that is a $\mathbb{Q}$-algebra and let $r \in \mathbb{Q}$. This is the formal power series
$t + \frac{r}{2} t^2$ over $R$, the second component of the generating pair
$[e^t, t + r t^2/2]$ of the exponential Pascal-type matrix. -/
noncomputable def exponentialPascalTypeSeries (r : ℚ) : PowerSeries R :=
  PowerSeries.X +
    PowerSeries.C (algebraMap ℚ R (r / 2)) * PowerSeries.X ^ 2

/-- **Generating pair of the exponential Pascal-type matrix.** Let $R$ be a commutative ring
that is a $\mathbb{Q}$-algebra and let $r \in \mathbb{Q}$. This is the pair of formal power
series $\left(e^t, t + \frac{r}{2} t^2\right)$ over $R$, written $[e^t, t + r t^2/2]$ in
exponential Riordan array notation. -/
noncomputable def exponentialPascalTypePair (r : ℚ) : PowerSeries R × PowerSeries R :=
  (PowerSeries.exp R, exponentialPascalTypeSeries R r)

/-- **Exponential Pascal-type matrix.** Let $R$ be a commutative ring that is a
$\mathbb{Q}$-algebra and let $r \in \mathbb{Q}$. The exponential Pascal-type matrix with
parameter $r$ is the exponential Riordan array $[e^t, t + r t^2/2]$ over $R$: the matrix with
rows and columns indexed by the natural numbers whose $(n, k)$ entry is

$$\frac{n!}{k!} \, [t^n] \, e^t \left(t + \frac{r}{2} t^2\right)^k,$$

where $[t^n]$ takes the coefficient of $t^n$ in a formal power series over $R$ and the
rational number $n!/k!$ acts on $R$ through its $\mathbb{Q}$-algebra structure. -/
noncomputable def exponentialPascalTypeMatrix (r : ℚ) : Matrix ℕ ℕ R :=
  fun n k =>
    algebraMap ℚ R ((n.factorial : ℚ) / k.factorial) *
      (PowerSeries.exp R * (exponentialPascalTypeSeries R r) ^ k).coeff n

end

end MetaMathlibExt
