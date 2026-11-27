# Correlation of two-locus coalescence times under partial selfing and recombination

**Model.** A one-sex diploid Wright–Fisher population of $N$ individuals with discrete generations. Backward in time, each child has a single parent (selfing) with probability $s_N$ and otherwise two distinct uniformly chosen parents. Each of the child's two chromosomes is, independently, a non-recombinant with probability $1-r_N$ (a uniformly chosen parental chromosome) or a recombinant with probability $r_N$ (the two loci copied from different chromosomes of the same parent). For two loci $i,j$ and two gene copies at each, $T_i, T_j$ are the pairwise coalescence times in generations; the joint ancestry is a 13-state Markov chain. Three sampling configurations are considered: $q_{12}$ (both chromosomes of one individual, both loci), $q_{11}$ (one chromosome from each of two individuals, both loci), $q_5$ (locus $i$ from both chromosomes of one individual, locus $j$ from both chromosomes of another). Let $R = (1-r)^2 + r^2$.

**Single locus.** With two copies in the same individual or in different individuals,

$$\mathbb{E}_{\rm same}[T_i] = 2(1-s_N)N + 2, \qquad \mathbb{E}_{\rm diff}[T_i] = (2-s_N)N + 1,$$

and for fixed $s_N = s\in[0,1)$, $\Pr_{\rm diff}(T_i > Nt)\to e^{-t/(2-s)}$ while $\Pr_{\rm same}(T_i > Nt)\to \frac{2(1-s)}{2-s}e^{-t/(2-s)}$: copies in one individual coalesce instantly (on the $N$-generation scale) with probability $s/(2-s)$.

**Theorem (asymptotic correlation, $N\to\infty$).** Let $s\in[0,1)$, $r\in(0,1]$, $\tilde\sigma,\tilde\rho\in(0,\infty)$.

1. $s_N = \tilde\sigma/N$, $r_N = \tilde\rho/N$:

$$\operatorname{Corr}_{q_{11}} = \operatorname{Corr}_{q_{12}} \to \frac{2\tilde\rho + 9}{8\tilde\rho^2 + 26\tilde\rho + 9}, \qquad \operatorname{Corr}_{q_5}\to\frac{2}{8\tilde\rho^2+26\tilde\rho+9}.$$

With $\rho = 4N r_N$ this is the classical $(\rho+18)/(\rho^2+13\rho+18)$.
2. $s_N = s$, $r_N = \tilde\rho/N$: the same formulas with $\tilde\rho$ replaced by $\tilde\rho(1-s)$ for $q_5, q_{11}$, while

$$\operatorname{Corr}_{q_{12}} \to \frac{4\tilde\rho^2 s(1-s)^2 + 12\tilde\rho s(1-s) + 2\tilde\rho(1-s) + 9}{8\tilde\rho^2(1-s)^2 + 26\tilde\rho(1-s) + 9}.$$

3. $s_N = \tilde\sigma/N$, $r_N = r$: correlations vanish, $\operatorname{Corr}_{q_{11}}\sim \frac{R}{2r(2-r)}\frac1N$, $\operatorname{Corr}_{q_{12}}\sim\frac{R(2r\tilde\sigma - 2r - r^2\tilde\sigma + r^2 + 1)}{2r(2-r)}\frac1N$, $\operatorname{Corr}_{q_5} = O(N^{-2})$.
4. $s_N = s$, $r_N = r$: $\operatorname{Corr}_{q_5}$ and $\operatorname{Corr}_{q_{11}}$ are $O(1/N)$ (explicit rational functions of $r,s$), but

$$\operatorname{Corr}_{q_{12}} \to \frac{(2-s)^2}{2(2-sR)} + s - 1 .$$

At the extremes, for every $N\ge2$: with no recombination ($r_N=0$), $\operatorname{Corr}_{q_{11}} = \operatorname{Corr}_{q_{12}} = 1$; with total selfing ($s_N=1$), $\operatorname{Corr}_{q_{12}} = \frac{3}{1+2r_N-2r_N^2} - 2$.

## Depends on

- [Covariance of the coalescence times, path form](../covariance-coalescence-times.md)

## Expansion

The covariances are computed exactly by first-step analysis on the 13-state chain ($\mathbb{E}_q[T_iT_j]$ solves a linear system in the transition matrix), and then expanded in $N$ under each of the four scalings; dividing by the single-locus variances, e.g. $\operatorname{Var}_{\rm same}[T_i] = 4(1-s_N)N^2 + 2(1-s_N)N + 2$ and $\operatorname{Var}_{\rm diff}[T_i] = (2-s_N)^2N^2 + (2-3s_N)N + 2$, gives the correlations. Recombination decouples the genealogies and selfing re-couples them: when $r = O(1)$ the correlation is $O(1/N)$ except for the configuration $q_{12}$ under strong selfing, where both pairs start in one individual and coalesce together through a run of selfing generations before any outcrossing separates them. For unlinked loci ($r = 1/2$, so $R = 1/2$), scenario 3 gives $\operatorname{Corr}_{q_{12}}\sim(3\tilde\sigma+1)/(12N)$: this is $1/(3N)$ at $\tilde\sigma = 1$ (where $\operatorname{Corr}_{q_{12}} = \operatorname{Corr}_{q_{11}}$), and its no-selfing value $1/(12N)$, the limit $\tilde\sigma\to0$, matches a previously known asymptotic lower bound for the Wright–Fisher model without selfing.

## Sources

- David Kogan, Dimitrios Diamantidis, John Wakeley and Wai-Tong Louis Fan, "Correlation of coalescence times in a diploid Wright–Fisher model with recombination and selfing", *Theoretical Population Biology* 167 (2026), 40–68, <https://doi.org/10.1016/j.tpb.2025.11.003>. Numbering as in the preprint arXiv:2310.12435v1, <https://arxiv.org/abs/2310.12435v1>: Section 2 (model), Lemmas 1–2, Theorems 1–2, Corollaries 1–2, Section 4.3 (equation (19)).
