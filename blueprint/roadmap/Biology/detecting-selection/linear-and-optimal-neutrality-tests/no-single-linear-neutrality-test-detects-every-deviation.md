# No single linear neutrality test detects every deviation

Let $a_n = \sum_{i=1}^{n-1} 1/i$, so the normalized neutral spectrum is $1/(i\,a_n)$. For linear neutrality tests $T_\Omega$ with weights $\sum_i \Omega_i = 0$:

1. If $n \ge 4$, then for every such weight vector $\Omega$ there exist numbers $\Delta_i$, not of the form $\text{const}/i$, and $\alpha \in [0,1]$ such that

$$\sum_i i\,\Omega_i\,\Delta_i = 0 \quad\text{and}\quad \min_{1 \le i \le n-1}\left(\alpha\,\frac{1}{i\,a_n} + (1-\alpha)\Delta_i\right) = 0.$$

Thus the spectrum $\xi_i = \alpha/(i a_n) + (1-\alpha)\Delta_i$, which completely lacks alleles in some frequency class, gives the test zero expected value and is undetectable by $T_\Omega$.

2. The same holds in the large-sample limit: for every piecewise continuous $\Omega(f) \in L^1[1/N, 1]$ with $\int_{1/N}^1 \Omega(f)\,df = 0$ there is a smooth $\Delta(f) \ne \text{const}/f$ and $\alpha \in [0,1]$ with $\int_{1/N}^1 f\,\Omega(f)\,\Delta(f)\,df = 0$ and $\inf_{f}\left(\alpha \frac{1}{f\log N} + (1-\alpha)\Delta(f)\right) = 0$.
3. Conversely, given at least $n-2$ linearly independent centred weight vectors, no $\Delta \ne \text{const}/i$ satisfies $\sum_i i\,\Omega_i\,\Delta_i = 0$ for all of them.

Hence linear tests must be designed against specific alternatives, or combined.

## Depends on

- [General linear neutrality tests and weight-consistent scaling](general-linear-neutrality-tests-and-weight-consistent-scaling.md)

## Expansion

The condition $\sum_i i\,\Omega_i\,\Delta_i = 0$ is one linear constraint on $\Delta \in \mathbb{R}^{n-1}$, so its solution space has dimension $n-2$; it always contains the neutral shape $\Delta_i = 1/i$, because $\sum_i \Omega_i = 0$. For $n \ge 4$ this space therefore contains a $\Delta$ not of the form $\text{const}/i$, and subtracting a multiple of $1/i$ gives it a negative entry; the mixed spectrum then has a positive minimum at $\alpha = 1$ and a negative one at $\alpha = 0$, so some $\alpha \in [0,1]$ makes it touch zero in some class. For $n = 3$ the hypothesis is needed: every centred weight vector is a multiple of $(1,-1)$, and the constraint forces $\Delta \propto (2,1)$, which is $\text{const}/i$. The centred weight vectors span the $(n-2)$-dimensional subspace orthogonal to the constant vector, and the vectors $i\Delta_i$ orthogonal to all of them are multiples of the constant vector, i.e. $\Delta_i \propto 1/i$, the neutral shape; this gives part 3.

## Sources

- S. E. Ramos-Onsins, G. Marmorini, G. Achaz and L. Ferretti, "A general framework for neutrality tests based on the site frequency spectrum", *Genes* 14 (2023), 1714, Section 2.3.1, Theorems 1–3, and Appendix A. <https://doi.org/10.3390/genes14091714> (PMC10531300)
