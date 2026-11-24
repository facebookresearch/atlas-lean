# A function holomorphic on a closed disc is the sum of its Cauchy power series

Let $E$ be a complex Banach space, $c \in \mathbb{C}$ and $R > 0$. For a function
$f \colon \mathbb{C} \to E$ and $n \ge 0$, the $n$-th coefficient of the Cauchy power series of $f$ on the
circle $|w - c| = R$ is the continuous $n$-linear map $p_n \colon \mathbb{C}^n \to E$ given by

$$p_n(v_1, \dots, v_n) = v_1 \cdots v_n \cdot \frac{1}{2 \pi i} \oint_{|w - c| = R} \frac{f(w)}{(w - c)^{n+1}} \, dw,$$

the circle being run through once counterclockwise. Let $D$ be the closed disc $|z - c| \le R$. If $f$
is complex differentiable within $D$ at each point of $D$, limits at the boundary points being taken
through $D$, then the power series $\sum_n p_n$ has radius of convergence at least $R$, and for every $z$
with $|z - c| < R$

$$f(z) = \sum_{n \ge 0} p_n(z - c, \dots, z - c) = \sum_{n \ge 0} (z - c)^n \, \frac{1}{2 \pi i} \oint_{|w - c| = R} \frac{f(w)}{(w - c)^{n+1}} \, dw,$$

the series converging in $E$.

## Sources

- Mathlib, `DifferentiableOn.hasFPowerSeriesOnBall` in `Mathlib.Analysis.Complex.CauchyIntegral`, at the
  pinned commit <https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/Analysis/Complex/CauchyIntegral.lean#L716-L718>, with the coefficients
  `cauchyPowerSeries` of `Mathlib.MeasureTheory.Integral.CircleIntegral`.
- L. V. Ahlfors, Complex Analysis, 3rd ed., Ch. 5, §1.2 (the Taylor series).
