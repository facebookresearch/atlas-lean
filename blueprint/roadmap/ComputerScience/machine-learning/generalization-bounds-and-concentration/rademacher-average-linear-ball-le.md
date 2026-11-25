# Rademacher average of a ball of linear predictors

Let $\varphi_1, \dots, \varphi_n$ be vectors of a real inner product space (the features $\varphi(x_i)$ of a sample) and let $D \ge 0$. For independent uniform signs $\varepsilon_1, \dots, \varepsilon_n \in \{-1, 1\}$ (the expectation being the average over the $2^n$ sign patterns),

$$
\mathbb{E}_\varepsilon \sup_{\|\theta\| \le D} \frac{1}{n} \sum_{i=1}^n \varepsilon_i \langle \theta, \varphi_i \rangle \le \frac{D}{n} \sqrt{\sum_{i=1}^n \|\varphi_i\|^2}.
$$

The left side is the empirical Rademacher complexity, on the sample, of the linear predictors $x \mapsto \langle \theta, \varphi(x) \rangle$ with $\|\theta\| \le D$. Proof: $\frac{1}{n} \sum_i \varepsilon_i \langle \theta, \varphi_i \rangle = \frac{1}{n} \langle \theta, \sum_i \varepsilon_i \varphi_i \rangle \le \frac{D}{n} \|\sum_i \varepsilon_i \varphi_i\|$ by the Cauchy–Schwarz inequality, and the average of $\|\sum_i \varepsilon_i \varphi_i\|$ over the signs is at most $\sqrt{\sum_i \|\varphi_i\|^2}$ because Hilbert spaces have Rademacher type $2$.

When $\|\varphi(x)\| \le R$ the bound is $D R / \sqrt{n}$, independent of the dimension of the feature space. It therefore covers balls of a reproducing kernel Hilbert space, where $\varphi(x)$ is the kernel function at $x$ and $\sum_i \|\varphi(x_i)\|^2 = \sum_i k(x_i, x_i)$ is the trace of the kernel matrix. With symmetrization and the contraction principle for a $G$-Lipschitz loss, it gives the estimation error $4 G R D / \sqrt{n}$ of constrained empirical risk minimization over linear predictors.

## Informally uses

- [Bound on the average Rademacher norm](../../../Analysis/banach-spaces/geometry-of-banach-spaces/rademacher-type-and-cotype/average-rademacher-norm-le.md): mathematical prerequisite, used verbatim for the average over the signs.

## Background

- [Aronszajn's theorem](../../../Analysis/hilbert-spaces/positive-definite-kernels/is-pos-def-kernel-iff-exists-feature-map.md): background, the feature map $\varphi$ of a positive-definite kernel, to which the bound applies.
- [Kernel Gram matrix](../../../Analysis/hilbert-spaces/representer-theorem/kernel-gram.md): background, the kernel matrix whose trace is $\sum_i \|\varphi(x_i)\|^2$.

## Sources

- F. Bach, *Learning Theory from First Principles*, MIT Press (2024); author PDF at <https://www.di.ens.fr/~fbach/ltfp_book.pdf>, Section 4.5.3, equation (4.16) ($\mathcal{R}_n(F) = \frac{D}{n} \mathbb{E}\|\Phi^\top \varepsilon\|_2 \le \frac{D}{\sqrt n} \sqrt{\mathbb{E} \|\varphi(x)\|_2^2}$; the form above is the same computation conditionally on the data), and Section 4.5.4, Proposition 4.5 (estimation error for linear predictions).
