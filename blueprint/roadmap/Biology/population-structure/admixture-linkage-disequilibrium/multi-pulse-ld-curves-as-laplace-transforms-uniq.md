# Identifiability and near-coincident rates in finite exponential mixtures

Let $0<T_1<\cdots<T_k$ and $w_i\in\mathbb R$.
If $\sum_i w_i e^{-T_i d}=0$ on a nonempty open interval, then every
$w_i=0$. Thus a finite exponential sum with distinct positive rates and
nonzero coefficients determines those rates and coefficients, up to
permutation. This applies to an admixture-decay curve only when the
finite-mixture representation is itself a stated model hypothesis.
It does not prove that every migration history has that form.

Nevertheless, for $0<\varepsilon\le1/2$,

$$\sup_{d\ge0}\left|\tfrac12e^{-(1-\varepsilon)d}
 +\tfrac12e^{-(1+\varepsilon)d}-e^{-d}\right|\le2\varepsilon^2.$$

The two-atom probability measure
$\mu_\varepsilon=(\delta_{1-\varepsilon}+\delta_{1+\varepsilon})/2$
and the one-atom measure $\mu_0=\delta_1$ have total-variation distance
$\sup_A|\mu_\varepsilon(A)-\mu_0(A)|=1$, although their Laplace curves
converge uniformly. Hence inversion is not continuous into total variation
at a coalescing-rate model and arbitrarily small curve errors cannot
reliably distinguish one pulse from two. This is not a claim of
instability in every parameter metric: their Wasserstein-1 distance is
$\varepsilon$, which does tend to zero.

## Background

- [Single-pulse exponential ancestry covariance](poisson-switch-markov-model-of-local-ancestry-al.md)

## Expansion

Choose a point $d_0$ inside the interval and differentiate $j=0,\ldots,k-1$
times. The unknowns $w_i e^{-T_i d_0}$ solve a Vandermonde system with
matrix $((-T_i)^j)_{j,i}$. Its determinant is nonzero for distinct rates,
so all coefficients vanish. Comparing two representations reduces to
this statement on the union of their rate sets.
For the bound, $\cosh u-1\le u^2e^{|u|}/2$ gives
$e^{-d}(\cosh(\varepsilon d)-1)\le\varepsilon^2 d^2e^{-d/2}/2$.
The maximum of $d^2e^{-d/2}$ is $16e^{-2}$, so the result follows from
$8e^{-2}<2$.

Injectivity for arbitrary finite measures on $[0,\infty)$ is the separate
[uniqueness theorem for Laplace transforms](../../../Analysis/harmonic-analysis/integral-transforms/laplace-transform/uniqueness-of-laplace-transforms-for-finite-nonn.md); the finite Vandermonde
argument above does not establish it.

## Related topics

- [Laplace transforms at the nonnegative integers determine a finite measure on the half-line](../../../Analysis/harmonic-analysis/integral-transforms/laplace-transform/uniqueness-of-laplace-transforms-for-finite-nonn.md)

## Sources

- P. Moorjani et al., *The history of African gene flow into Southern Europeans, Levantines, and Jews*, PLoS Genetics 7 (2011), e1001373, <https://doi.org/10.1371/journal.pgen.1001373>, Results, p. 4, reports unreliable fitting of multiple exponentials to noisy data. The uniqueness theorem, explicit bound and topology distinction are derived here.
