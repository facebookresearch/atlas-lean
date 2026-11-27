# Bounded convergence in probability implies convergence of means

Let $(\Omega, P)$ be a probability space, $x$ a real number, and
$X_N \colon \Omega \to \mathbb{R}$ a measurable function for every natural number $N$. Suppose
that for all large $N$, $|X_N - x| \le 1$ almost surely, and that $X_N \to x$ in probability:
$P(|X_N - x| \ge \varepsilon) \to 0$ for every $\varepsilon > 0$. Then

$$\int_\Omega X_N \, dP \to x \quad \text{as } N \to \infty.$$

For all large $N$ these integrals are the expectations $E[X_N]$ of bounded random variables; for
the finitely many other $N$, where $X_N$ need not be integrable, the integral of a non-integrable
function is $0$ by convention, which does not affect the limit.
