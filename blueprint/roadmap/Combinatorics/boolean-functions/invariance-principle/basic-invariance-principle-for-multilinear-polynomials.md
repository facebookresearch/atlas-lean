# Basic invariance principle for low-degree multilinear polynomials

Let $Q$ be a formal multilinear polynomial of degree at most $k$ with variance at most $1$ and all influences at most $\varepsilon$. Let $\mathbf{X}$ and $\mathbf{Y}$ be vectors of independent random variables satisfying the invariance hypothesis. Then the Lévy distance between $Q(\mathbf{X})$ and $Q(\mathbf{Y})$ is at most $4\cdot 2^k \varepsilon^{1/5}$. In particular for $f : \{-1,1\}^n \to \mathbb{R}$ of degree at most $k$, $\mathrm{Var}[f] \le 1$ and all influences at most $\varepsilon$, the distribution of $f$ on uniform bits is within Lévy distance $4 \cdot 2^k\varepsilon^{1/5}$ of the distribution of its Fourier polynomial evaluated at independent Gaussians.

## Proof sketch

Replace variables one at a time as in Lindeberg's method; the error at step $i$ is controlled by the fourth moment of the part of $Q$ depending on $z_i$, which by hypercontractivity of the invariance ensemble ($9$-reasonable variables) is at most $9^k\mathrm{Inf}_i[Q]^2$; summing gives $9^k\sum_i\mathrm{Inf}_i[Q]^2\le9^k\varepsilon\sum_i\mathrm{Inf}_i[Q]\le k\,9^k\varepsilon$ for $C^4$ tests (the total influence of $Q$ is at most $k\,\mathrm{Var}[Q]\le k$), and smoothing a step function gives the Lévy bound.

## Depends on

- [Lévy distance and the hypothesis of the basic invariance principle](levy-distance-and-invariance-hypothesis.md)
- [Boolean degree](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/fourier-analysis-on-the-boolean-cube/boolean-degree.md)

## Proof depends on

- [Invariance principle for sums of independent random variables](invariance-principle-for-sums.md)
- [Bonami Lemma](../../../Probability/concentration-inequalities/bonami-beckner-hypercontractivity/bonami-lemma.md)

## Sources

- R. O'Donnell, "Analysis of Boolean Functions", Cambridge University Press, 2014.
