# The sub-additive closure is the largest good minorant

Let $f$ be in the set $\mathcal F$ of [min-plus convolution](min-plus-convolution-and-deconvolution.md) and $\bar f$ its [sub-additive closure](sub-additive-closure.md). Then $\bar f \le f$, $\bar f \in \mathcal F$ and $\bar f$ is sub-additive with $\bar f(0) = 0$; and every sub-additive $g \in \mathcal F$ with $g(0) = 0$ and $g \le f$ satisfies $g \le \bar f$. Consequently, for $f \in \mathcal F$ the following are equivalent: $f(0) = 0$ and $f$ is sub-additive; $f(0) = 0$ and $f \otimes f = f$; $\bar f = f$. (Idempotence alone is not enough: $\varepsilon \otimes \varepsilon = \varepsilon$ while $\bar\varepsilon = \delta_0$; the source's proof infers $f(0) = 0$ from $f(0) + f(0) = f(0)$, which fails when $f(0) = +\infty$.)

## Depends on

- [Sub-additive closure](sub-additive-closure.md)

## Proof depends on

- [Algebraic properties of min-plus convolution](algebraic-properties-of-min-plus-convolution.md): closure of $\mathcal F$ under $\otimes$.

## Sources

- J.-Y. Le Boudec and P. Thiran, *Network Calculus: A Theory of Deterministic Queuing Systems for the Internet*, Lecture Notes in Computer Science 2050, Springer, 2001; online version of 2022, <https://leboudec.github.io/netcal/latex/netCalBook.pdf>, whose numbering is used here, Section 3.1.8, Theorem 3.1.10 and Corollary 3.1.1, with their proofs.
