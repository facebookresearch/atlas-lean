# Jensen's formula

Jensen's formula expresses the average of $\log|f|$ over a circle through the value of $f$ at the centre and the zeros of $f$ inside the circle, counted with multiplicity. In its classical form, let $R > 0$ and let $f$ be holomorphic on an open set containing the closed disc $\{z : |z| \le R\}$, with $f(0) \ne 0$ and $f(z) \ne 0$ whenever $|z| = R$. If $z_1, \dots, z_N$ are the zeros of $f$ in the open disc $\{z : |z| < R\}$, each listed as many times as its order, then

$$\log|f(0)| = \sum_{k=1}^{N} \log\frac{|z_k|}{R} + \frac{1}{2\pi}\int_0^{2\pi} \log|f(Re^{i\theta})|\,d\theta.$$

Mathlib proves the formula for a disc with any centre and allows zeros on the circle. Let $c \in \mathbb{C}$, let $R$ be a real number, let $D = \{z : |z - c| \le |R|\}$, and let $f \colon \mathbb{C} \to \mathbb{C}$ be analytic at every point of $D$ with $f(c) \ne 0$. Let $Z$ be the set of zeros of $f$ in $D$, and for $u \in Z$ let $m(u) \ge 1$ be the order of vanishing of $f$ at $u$. The set $Z$ is finite and does not contain $c$. Then

$$\frac{1}{2\pi}\int_0^{2\pi} \log|f(c + Re^{i\theta})|\,d\theta = \sum_{u \in Z} m(u)\,\log\frac{R}{|c - u|} + \log|f(c)|.$$

Here $\log$ is Mathlib's real logarithm, which satisfies $\log 0 = 0$ and $\log x = \log|x|$ for every real $x$; the second rule covers a negative $R$. Zeros on the circle $|z - c| = |R|$ contribute $m(u)\log 1 = 0$ to the sum; they make the integrand singular, but its logarithmic singularities are integrable. The radius may be negative or zero: the disc has radius $|R|$, and for $R = 0$ the only point of $D$ is $c$, so $Z$ is empty, the sum is $0$ and both sides equal $\log|f(c)|$. For $c = 0$, $R > 0$ and no zeros on the circle, $Z$ consists of the zeros $z_k$ in the open disc, and $\log(R/|z_k|) = -\log(|z_k|/R)$, so moving the sum to the other side gives the classical formula.

## Sources

- Elias M. Stein and Rami Shakarchi, Complex Analysis, Princeton Lectures in Analysis II, Princeton University Press, 2003.
- The mathlib Community, *mathlib4* at revision fc4f59e577feb1a4956671bc04ac18aaaf8cd842, for the average of a function over a circle: `circleAverage`, https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/MeasureTheory/Integral/CircleAverage.lean#L50-L56.
- The mathlib Community, *mathlib4* at revision fc4f59e577feb1a4956671bc04ac18aaaf8cd842, for the divisor of an analytic function at a point as its order of vanishing: `AnalyticOnNhd.divisor_apply`, https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/Analysis/Meromorphic/Divisor.lean#L79-L80.
- The mathlib Community, *mathlib4* at revision fc4f59e577feb1a4956671bc04ac18aaaf8cd842, for the convention $\log 0 = 0$: `Real.log_zero`, https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/Analysis/SpecialFunctions/Log/Basic.lean#L102.
- The mathlib Community, *mathlib4* at revision fc4f59e577feb1a4956671bc04ac18aaaf8cd842, for the convention $\log |x| = \log x$: `Real.log_abs`, https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/Analysis/SpecialFunctions/Log/Basic.lean#L114.
