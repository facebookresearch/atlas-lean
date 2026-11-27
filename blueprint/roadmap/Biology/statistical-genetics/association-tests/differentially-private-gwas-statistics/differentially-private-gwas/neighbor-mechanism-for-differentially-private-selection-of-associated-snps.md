# Neighbor mechanism for differentially private selection of associated SNPs

**Differential privacy.** Two genotype databases are neighbours if they differ in one individual. A
randomized function $F$ is $\epsilon$-differentially private if for all neighbouring $D, D'$ and all
measurable sets $S$,

$$\Pr(F(D) \in S) \le e^{\epsilon} \Pr(F(D') \in S).$$

The Laplace mechanism releases $f(D) + \mathrm{Lap}_k(\Delta f/\epsilon)$, where
$\Delta f = \max_{D, D' \text{ neighbors}} \lVert f(D) - f(D') \rVert_1$ is the $\ell_1$ sensitivity and $\mathrm{Lap}_k(\lambda)$
has density proportional to $e^{-\lVert x \rVert_1/\lambda}$; it is $\epsilon$-differentially private.

**Allelic test statistic.** For one SNP in a case–control study, let $r_0, r_1, r_2$ (summing to $R$)
and $s_0, s_1, s_2$ (summing to $S$) be the numbers of individuals in the two cohorts carrying
$0, 1, 2$ copies of one allele, $N = R + S$, and $x = 2r_0 + r_1$, $y = 2s_0 + s_1$ the corresponding
allele counts. The allelic test statistic is

$$Y(x, y) = \frac{2N\,(xS - yR)^2}{R\,S\,(x + y)(2N - x - y)} .$$

**Neighbor mechanism.** Fix a significance threshold $\omega$. The neighbor distance $d_i$ of SNP $i$
is the minimum number of individuals whose genotypes must change (cohort sizes fixed) to move
$Y_i$ across $\omega$, taken positive for SNPs above $\omega$ and as $1 - d$ for SNPs below it. To
release $m$ SNPs, sample $m$ SNPs without replacement with probabilities proportional to

$$\exp\Bigl(\frac{\epsilon\, d_i}{2m}\Bigr);$$

the output is $\epsilon$-differentially private. In the modified mechanism, a budget $\epsilon_1$ is
spent on a Laplace-noised estimate of the threshold (the midpoint between the $m$-th and $(m+1)$-st
largest scores) and $\epsilon_2$ on the selection, for total privacy $\epsilon_1 + \epsilon_2$.

**Fast neighbor distance.** Changing one genotype moves $(x, y)$ by at most $2$ in one coordinate, and
the neighbor distance is the integer program

$$\min_{\rho' \in \mathbb{Z}^6_{\ge 0}} \tfrac{1}{2}\lVert \rho - \rho' \rVert_1 \quad\text{s.t.}\quad
\textstyle\sum_{j} r_j' = R,\ \sum_j s_j' = S,\ \operatorname{sgn}\bigl(Y(\rho) - \omega\bigr)\bigl(Y(x', y') - \omega\bigr) \le 0 .$$

Its relaxation is a separable piecewise-linear convex cost $g_1(x) + g_2(y)$ minimized over the region
cut out by the conic $2N(xS - yR)^2 = RS\,\omega\,(x + y)(2N - x - y)$; the optimum lies at a point of the
conic with tangent slope in $\{1/2, 1, 2\}$ or on a breakpoint line of $g_1$ or $g_2$, so the distance is
found with a constant number of arithmetic operations per SNP (for $\omega \ge 2N/(2N - 1)$), followed
by an integer rounding step.

## Depends on

- [Differential privacy](../../../../../ComputerScience/cryptography/differential-privacy/differentially-private.md)
- [The Laplace mechanism for vector-valued queries](../../../../../ComputerScience/cryptography/laplace-and-exponential-mechanisms/laplace-mechanism-pi-differentially-priv.md)

## Proof depends on

- [The exponential mechanism is differentially private](../../../../../ComputerScience/cryptography/laplace-and-exponential-mechanisms/exp-mechanism-differentially-private.md)
- [Adaptive composition of pure differential privacy](../../../../../ComputerScience/cryptography/differential-privacy/comp-prod.md)

## Expansion

The selection step is an exponential mechanism with score $d_i$: changing one individual changes
each neighbor distance by at most one, so each draw is $\epsilon/m$-private and $m$ draws compose
to $\epsilon$. Using neighbor distances rather than noisy test statistics ties the score to the
quantity that matters for privacy, how many participants would have to differ to change a SNP's
significance, and makes strongly associated SNPs very likely to be returned. Its computational
bottleneck, exact neighbor distances for hundreds of thousands of SNPs, disappears because the
relaxed problem is convex in each coordinate and its minimizer can be enumerated from a fixed list of
candidate points obtained in closed form with the quadratic formula.

## Sources

- S. Simmons, B. Berger, "Realizing privacy preserving genome-wide association studies",
  Bioinformatics 32 (2016) 1293-1300, Definition 1, Theorem 1, Section 3.2 (allelic test statistic)
  and Algorithms 1-3, <https://doi.org/10.1093/bioinformatics/btw009> (PMC4848404).
