# False-positive bound for multipool testing

Let a population of $N$ samples, a pool size $n$ and a multiplicity $k$ be given with $n \mid Nk$. An **$(N, n, k)$-multipool** is a collection of pools (subsets of the samples) such that (M1) every pool has exactly $n$ samples, (M2) every sample lies in exactly $k$ pools, and (M3) any two distinct samples lie together in at most one pool. All $Nk/n$ pools are tested once, in parallel, with an error-free test, and a sample is declared positive if and only if all $k$ of its pools test positive (combinatorial orthogonal matching pursuit decoding). Suppose each sample is infected independently with probability $\rho$.

**Proposition.** No infected sample is missed. A given uninfected sample is declared positive with probability $\big(1 - (1-\rho)^{n-1}\big)^{k}$, so the probability that a positive result is a false positive is

$$\frac{(1-\rho)\big(1 - (1-\rho)^{n-1}\big)^{k}}{\rho + (1-\rho)\big(1 - (1-\rho)^{n-1}\big)^{k}} .$$

**Theorem.** Let $\rho \le \tfrac12$ and $0 < \epsilon_{\mathrm{fp}} < 1$. If

$$k \;\ge\; \frac{\ln\frac{\epsilon_{\mathrm{fp}}}{1-\epsilon_{\mathrm{fp}}} + \ln\frac{\rho}{1-\rho}}{\ln\big(1 - (1-\rho)^{n-1}\big)},$$

then in every $(N, n, k)$-multipool strategy the probability that a positive result is a false positive is at most $\epsilon_{\mathrm{fp}}$. The right-hand side is increasing in $\rho$ on $(0, \tfrac12]$, so an upper bound on the incidence suffices.

The design uses $Nk/n$ tests, a saving of a factor $n/k$ over individual testing; with $n\rho \approx C$ fixed the required $k$ grows only logarithmically in $1/\rho$.

## Expansion

An infected sample makes all its pools positive, so there are no false negatives. For an uninfected sample, its $k$ pools contain disjoint sets of $n - 1$ other samples by (M3), so the events "pool $j$ contains another infected sample" are independent, each with probability $1 - (1-\rho)^{n-1}$; this gives the false-positive probability and, by Bayes' rule, the stated ratio. Requiring the ratio to be at most $\epsilon_{\mathrm{fp}}$ and rearranging gives $\big(1 - (1-\rho)^{n-1}\big)^k \le \epsilon_{\mathrm{fp}}\rho / ((1 - \epsilon_{\mathrm{fp}})(1-\rho))$; taking logarithms (the base is in $(0,1)$, which flips the inequality) gives the bound on $k$. In design language a multipool is a $(k-1)$-disjunct matrix, which identifies all infected samples exactly when there are at most $k - 1$ of them; the probabilistic bound covers the regime where the number of infections exceeds $k$.

## Sources

- M. Täufer, "Rapid, large-scale, and effective detection of COVID-19 via non-adaptive testing", Journal of Theoretical Biology 506 (2020) 110450, Definition 1, Eqs. (3.6)–(3.10) and Theorem 1, <https://doi.org/10.1016/j.jtbi.2020.110450>, PMCID PMC7428746.
