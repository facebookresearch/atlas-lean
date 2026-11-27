# Expected breakpoints after random DCJ operations

Model a genome on $2g$ gene extremities as a matching of **adjacencies**: $a$ observed adjacencies between consecutive genes, completed to a perfect matching of $n$ adjacencies by adding telomeric and $f$ fictional elements (with $f$ and the number of telomeres $o(n)$). A **double cut-and-join (DCJ)** replaces two distinct adjacencies $AB, CD$ by $AC, BD$ or by $AD, BC$. In the **mechanistic DCJ model**, each step picks one of the $n(n-1)$ equiprobable DCJs on the completed genome, so genomes evolve as a Markov chain on perfect matchings. A **breakpoint** of $G$ with respect to $G'$ is an observed adjacency $AB$ of $G$ such that $A$ and $B$ are not adjacent in $G'$.

**Theorem.** If $G_k$ is obtained from $G$ by $k$ random DCJs, the expected number of breakpoints is

$$\mathbb E[B_k] = a\,\frac{2n - 2}{2n - 1}\left[1 - \left(1 - \frac{1}{n-1} - \frac1n\right)^{k}\right].$$

Inverting it gives the distance estimator

$$\widetilde{\mathrm{DCJ}}(G_1, G_2) = \frac{\log\!\Big(1 - \dfrac{B\,(2n-1)}{a\,(2n-2)}\Big)}{\log\!\Big(1 - \dfrac{1}{n-1} - \dfrac1n\Big)}$$

from the observed number $B$ of breakpoints.

**Proposition (binary-sequence coding).** Coding adjacencies as sites of a binary sequence evolving by single-site flips, $\mathbb E[D_{k_s}] = \tfrac N2\big(1 - (1 - \tfrac2N)^{k_s}\big)$ differences after $k_s$ flips. This equals twice the DCJ breakpoint expectation if the sequence length is $N = 4a\frac{2n-2}{2n-1}$ ($\approx 4a$) and $k_s = k\,\dfrac{\log(1 - 1/n - 1/(n-1))}{\log(1 - 2/N)}$ ($\approx 4ka/n$); coding all absent adjacencies as sites, or none, biases the distance.

## Depends on

- [Double-cut-and-join distance formula](double-cut-and-join-distance-formula.md)

## Expansion

Let $P_k$ be the probability that a given adjacency of $G$ is absent in $G_k$; by symmetry it does not depend on the adjacency, so $\mathbb E[B_k] = aP_k$. One DCJ cuts a present adjacency with probability $p_s = 2(n-1)/(n(n-1)) = 2/n$ and recreates an absent one with probability $1/(n(n-1))$, so $P_k = P_{k-1}(q_u - p_s) + p_s$ with $q_u = 1 - \frac{1}{n(n-1)}$ and $P_0 = 0$. Solving this linear recurrence gives $P_k = \frac{p_s}{1 - q_u + p_s}\big(1 - (q_u - p_s)^k\big)$, and $q_u - p_s = 1 - \frac{1}{n-1} - \frac1n$. The factor four reflects that one DCJ changes four adjacency sites at once (two removed, two created), so a single-site substitution model matches it only after rescaling length and time by four, as in the Jukes–Cantor style saturation correction.

## Sources

- P. Biller, L. Guéguen, E. Tannier, "Moments of genome evolution by Double Cut-and-Join", BMC Bioinformatics 16 (Suppl 14) (2015) S7, Theorem 1 (Eqs. 1–3), the distance estimator, and the Proposition (Eq. 4), <https://doi.org/10.1186/1471-2105-16-S14-S7>, PMCID PMC4602343.
