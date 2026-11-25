# Optional stopping for submartingales at a bounded stopping time

Let $(X_n)_{n \ge 0}$ be a submartingale with respect to a filtration $(\mathcal F_n)_{n \ge 0}$, and let
$N$ be a stopping time, a random variable with values in $\{0, 1, 2, \dots\} \cup \{\infty\}$ such that
$\{N = n\} \in \mathcal F_n$ for every $n$. If $P(N \le k) = 1$ for some integer $k \ge 0$, then
$X_N = X_{N(\omega)}(\omega)$, which is defined almost surely, is integrable, and

$$E X_0 \le E X_N \le E X_k.$$

## Proof

Almost surely $X_N = \sum_{n=0}^{k} X_n 1_{\{N = n\}}$, a random variable, and $|X_N| \le |X_0| + \dots + |X_k|$, so
$X_N$ is integrable, by monotonicity and additivity of the integral. The stopped process $(X_{N \wedge n})_{n \ge 0}$ is
a submartingale, and the expected values of a submartingale increase, so
$E X_0 = E X_{N \wedge 0} \le E X_{N \wedge k} = E X_N$. For the other inequality, $K_n = 1_{\{N \le n-1\}}$ is a
bounded nonnegative predictable sequence, because $\{N \le n - 1\} \in \mathcal F_{n-1}$. The transform of a
submartingale by a bounded nonnegative predictable sequence is a submartingale, so
$(K \cdot X)_n = \sum_{m=1}^{n} K_m (X_m - X_{m-1}) = X_n - X_{N \wedge n}$ is one; it vanishes at time $0$, so, by
linearity of the expected value, $E X_k - E X_N = E (K \cdot X)_k \ge 0$.

## Depends on

- [Martingales, submartingales and supermartingales](../martingales-submartingales-and-supermartingales/martingale.md)
- [Expected value of a random variable](../../foundations/laws-of-random-variables-and-identical-distribut/expectation/expectation-random-variable.md)

## Proof depends on

- [Stopped submartingales are submartingales](stopped-process.md)
- [Expectations increase along a submartingale](../martingale-convergence-theorems/integral-mono.md)
- [Predictable sequence](../martingales-submartingales-and-supermartingales/predictable-sequence.md)
- [Bounded nonnegative predictable transforms of a submartingale](../martingales-submartingales-and-supermartingales/sum-mul-sub.md)
- [Monotonicity of the integral](../../../MeasureTheory/integration/nonnegative-lebesgue-integral/lebesgue-integral/lintegral-mono.md)
- [Additivity and positive homogeneity of the integral](../../../MeasureTheory/integration/nonnegative-lebesgue-integral/additivity-of-the-integral/integral-nonnegative-additive-homogeneous.md)
- [Additivity of the integral of integrable functions](../../../MeasureTheory/integration/nonnegative-lebesgue-integral/additivity-of-the-integral/integral-add.md)
- [Homogeneity of the integral](../../../MeasureTheory/integration/nonnegative-lebesgue-integral/additivity-of-the-integral/integral-smul.md)

## Sources

- R. Durrett, *Probability: Theory and Examples*, 5th ed., Theorem 4.4.1, with the definition of a stopping time in Section 4.2 (version read: the author's January 2019 PDF).
