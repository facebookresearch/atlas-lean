# Differential privacy

A *mechanism* is a map $M : X \to \mathcal{M}(\Omega)$ sending a database $x$ to a measure $M(x)$
on $\Omega$, the law of the released output (the definition below applies to arbitrary measures;
for a mechanism they are probability measures). For a neighbouring relation $\mathrm{Adj}$ on databases, $\varepsilon \in \mathbb{R}$
and $\delta \in [0, \infty]$, the mechanism is $(\varepsilon, \delta)$-differentially private if for
all $x, y$ with $\mathrm{Adj}(x, y)$ and every measurable $S \subseteq \Omega$,

$$
M(x)(S) \le e^{\varepsilon} M(y)(S) + \delta .
$$

With $\delta = 0$ this is $\varepsilon$-differential privacy. Dwork and Roth state the definition for
histogram databases $x \in \mathbb{N}^{|\mathcal{X}|}$ with $\|x - y\|_1 \le 1$, the relation of
[neighbouring histograms](histogram-adj.md); databases given as lists of rows use the
[Hamming relation](hamming-adj.md).
The probability is over the coins of the mechanism only: the database is fixed, not random.

## Background

- [Total variation distance between finite measures](../../../Probability/convergence-of-measures/total-variation-distance/total-variation-dist.md): for probability measures and a symmetric neighbouring relation, the case $\varepsilon = 0$ of the definition says that $M(x)$ and $M(y)$ are at total variation distance at most $\delta$.

## Sources

- C. Dwork and A. Roth, *The Algorithmic Foundations of Differential Privacy*, Foundations and Trends in Theoretical Computer Science 9(3–4), 2014, <https://www.cis.upenn.edu/~aaroth/privacybook.html>, Definition 2.4 (with Definition 2.2 for randomized algorithms and Definition 2.3 for the $\ell_1$ distance of histograms).
- C. Dwork, F. McSherry, K. Nissim and A. Smith, *Calibrating noise to sensitivity in private data analysis*, TCC 2006 (the original definition, cited in Dwork and Roth 2014, Section 2.4).
