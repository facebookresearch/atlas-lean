# Local de Moivre–Laplace theorem for a fair coin

This is the local theorem for a fair coin, success probability $p = 1/2$. For natural numbers $n$ and
$k$ let $b(n, k) = \binom{n}{k}/2^n$, the probability that a binomial count with parameters $n$ and
$1/2$ equals $k$, and let

$$g(n, k) = \sqrt{\frac{2}{\pi n}}\, \exp\Big(-\frac{(k - n/2)^2}{n/2}\Big)$$

be its Gaussian approximation. Fix $x \in \mathbb{R}$ and let $k_n = \lfloor n/2 + x \sqrt{n}/2 \rfloor$
(read as $0$ when the argument is negative). Then $b(n, k_n)/g(n, k_n) \to 1$ as $n \to \infty$.

## Idea

The integral de Moivre–Laplace theorem approximates probabilities of intervals; the local theorem
approximates single point masses. A binomial count with parameters $n$ and $1/2$ has mean $n/2$ and
standard deviation $\sqrt{n}/2$, and $g(n, k)$ is the normal density with the same mean and variance,
evaluated at $k$. The theorem says that at the lattice point $k_n$, about $x$ standard deviations from
the mean, the point mass is asymptotic to this density value, which is about
$\sqrt{2/(\pi n)}\, e^{-x^2/2}$. One proof applies Stirling's formula to the three factorials in
$\binom{n}{k_n}$ and expands the resulting logarithmic entropy term to second order; the cubic
remainder is negligible because $k_n - n/2$ is of order $\sqrt{n}$. A companion statement treats the
simple random walk $S$: if $2k_n/\sqrt{2n} \to x$, then $P(S_{2n} = 2k_n) \sim e^{-x^2/2}/\sqrt{\pi n}$.

## Statements

- [Local De Moivre–Laplace theorem for $p = 1/2$](local-de-moivre-laplace-half.md)
- [Local limit theorem for the simple random walk](local-de-moivre-laplace-half-of-tendsto.md): local limit theorem for the simple random walk (convergent displacement)
- [Binomial point mass with success probability one half](binom-prob-half.md): definition used in the main statement
- [Gaussian approximation to the symmetric binomial point mass](gaussian-approx-half.md): definition used in the main statement
- [Stirling decomposition of the binomial-to-Gaussian ratio](binom-prob-div-gaussian-approx-eq.md): lemma used in the proof
- [Binomial point mass is equivalent to its Gaussian approximation](binom-prob-half-is-equivalent-gaussian-a.md): lemma used in the proof of the main statement
- [Binomial point mass is equivalent to a fixed Gaussian value](binom-prob-half-is-equivalent-fixed-gaus.md): variant with a fixed Gaussian value
- [The corrected binomial power factor tends to one](dml-power-factor-tendsto-one.md): the limit of the power factor in the Stirling decomposition, the analytic step of the proof sketched above
- [Cubic bound on the symmetric entropy residual](entropy-residual-bound.md): lemma used in the proof
- [Factorial in terms of the Stirling sequence](factorial-eq-stirling-seq-mul.md): lemma used in the proof (Stirling)
- [Logarithm of the binomial power factor](log-power-factor-formula.md): lemma used in the proof
- [Lattice index in the local De Moivre–Laplace theorem](local-dmlindex.md): definition used in the main statement
- [Deviation bound for the De Moivre–Laplace index](local-dmlindex-deviation-bound.md): basic property of the lattice index
- [The De Moivre–Laplace index over n tends to one half](local-dmlindex-ratio-half.md): lemma about the lattice index
- [Standardized displacement of the rounded index converges](local-dmlindex-standardized-tendsto.md): lemma about the lattice index
- [The De Moivre–Laplace index tends to infinity](local-dmlindex-tendsto-at-top.md): lemma about the lattice index
- [The complementary index over n tends to one half](n-sub-local-dmlindex-ratio-half.md): lemma about the lattice index
- [The complementary De Moivre–Laplace index tends to infinity](n-sub-local-dmlindex-tendsto-at-top.md): lemma about the lattice index
