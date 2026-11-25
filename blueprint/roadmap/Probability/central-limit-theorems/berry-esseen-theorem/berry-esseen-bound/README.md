# Berry–Esseen theorem

There is a constant $C > 0$ with the following property. Let $X_0, X_1, X_2, \dots$ be measurable,
mutually independent real random variables on a probability space, all with the same distribution,
such that $X_0$ has a finite third absolute moment $\rho = \mathbb{E}|X_0|^3$, mean
$\mathbb{E}[X_0] = 0$ and variance $\sigma^2 = \operatorname{Var}(X_0) > 0$, with $\sigma > 0$. Write
$S_n = X_0 + \dots + X_{n-1}$ and $\Phi$ for the distribution function of the standard normal
distribution. Then for every $n \ge 1$ and every real $x$,

$$\left|\mathbb{P}\left(\frac{S_n}{\sigma\sqrt{n}} \le x\right) - \Phi(x)\right| \le \frac{C\rho}{\sigma^3\sqrt{n}}.$$

## Idea

The central limit theorem says that the distribution function of the standardized sum
$S_n/(\sigma\sqrt{n})$ converges to $\Phi$, but it gives no rate. The Berry–Esseen theorem gives one,
uniformly in $x$: the error is at most a constant times $\rho/(\sigma^3\sqrt{n})$, so it is of order
$1/\sqrt{n}$, and the law of $X_0$ enters only through the scale-free ratio $\rho/\sigma^3$. The order
$1/\sqrt{n}$ cannot be improved: for fair $\pm 1$ coin flips and even $n$, the sum is $0$ with
probability about $\sqrt{2/(\pi n)}$, so its distribution function jumps by that much at a point where
$\Phi$ is continuous. The classical proof compares characteristic functions near the origin and turns
that comparison into a bound on distribution functions with Esseen's smoothing inequality. The explicit
form in this card takes $C = 42$; much smaller constants are known.

## Statements

- [Berry–Esseen theorem](berry-esseen.md)
- [Berry–Esseen theorem with constant 42](berry-esseen-explicit.md): explicit form with constant 42
- [Berry–Esseen bound for finite sums](berry-esseen-finset-sum-gaussian.md): non-identically distributed finite sums; used in the proof of the explicit form

## Background

- [Lindeberg–Feller central limit theorem](../../lindeberg-feller-central-limit-theorem/README.md):
  the central limit theorem whose rate of convergence this card quantifies.

## Sources

- A. C. Berry, "The accuracy of the Gaussian approximation to the sum of independent variates",
  Transactions of the American Mathematical Society (1941).
- C.-G. Esseen, "On the Liapounoff limit of error in the theory of probability", Arkiv för
  Matematik, Astronomi och Fysik (1942).
