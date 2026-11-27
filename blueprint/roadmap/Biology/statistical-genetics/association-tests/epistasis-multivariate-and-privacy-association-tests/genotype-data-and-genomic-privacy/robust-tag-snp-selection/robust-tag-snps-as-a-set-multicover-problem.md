# Robust tag SNPs as a set multicover problem

A haplotype block is an $N \times K$ matrix $M$ with $M[k, j] \in \{1, 2\}$ the allele of SNP $k$ in haplotype pattern $j$. Let $\mathcal P = \{(i, j) : 1 \le i < j \le K\}$ be the pattern pairs, and for each SNP $S_k$ let $S'_k = \{(i, j) \in \mathcal P : M[k, i] \ne M[k, j]\}$ be the pairs it distinguishes. A set $C'$ of SNPs is a set of **robust tag SNPs** tolerating $m$ missing calls if every pair of patterns is still distinguished by some SNP of $C'$ after any $m$ SNPs of $C'$ are discarded. **MRTS** (minimum robust tag SNPs) asks for a smallest such $C'$.

**Lemma 1.** $C'$ tolerates $m$ missing SNPs if and only if every pair $(i, j) \in \mathcal P$ is distinguished by at least $m + 1$ SNPs of $C'$; MRTS is thus set multicover with demand $m + 1$ on the universe $\mathcal P$.

**Lemma 2.** At least $\lceil\log_2 K\rceil$ tag SNPs are needed to distinguish $K$ patterns.

**Theorem 1.** MRTS is NP-hard (for $m = 0$ it is the minimum test set problem).

**Theorems 2–4 (approximations).** With $|\mathcal P| = K(K-1)/2$:
- filling the $m+1$ coverage rows one at a time, each by greedy set cover, gives a $(m+1)\ln\frac{K(K-1)}{2}$-approximation;
- greedily picking the SNP that covers the most still-deficient demand units gives a $\ln\frac{(m+1)K(K-1)}{2}$-approximation;
- iterated LP relaxation with randomized rounding gives an $O(m\ln K)$-approximation.

**Theorem 5.** Choosing the fewest additional SNPs to make a given tag set robust (MATS) is also NP-hard.

## Depends on

Its statement uses only the notions recalled above.

## Proof depends on

- [MINIMUM TEST SET is NP-complete](../../../../../../TheoryOfComputation/np-completeness/set-systems-and-location/minimum-test-set/minimum-test-set-np-complete.md)
- [Harmonic bound in the largest set size for greedy set cover](../../../../../../ComputerScience/approximation-algorithms/greedy-set-cover/greedy-set-cover-approx.md)

## Expansion

If some pair were separated by only $m$ tags, losing exactly those tags would leave it unresolved, and conversely $m + 1$ separating tags survive any $m$ losses, giving Lemma 1. Lemma 2 counts: $t$ binary SNPs realize at most $2^t$ distinct patterns. The greedy bounds follow the standard set-cover charging argument: when $R$ demand units remain uncovered, some SNP of an optimal solution $C^*$ covers at least $R/|C^*|$ of them, so the greedy choice does too; charging each newly covered unit $|C^*|/R$ and summing harmonic numbers bounds the total by $|C^*|\,H(\text{demand})$. For the LP, each covering inequality fails after randomized rounding with probability below $e^{-(m+1)/2}$, and repetition yields the $O(m\ln K)$ factor. In practice a few additional tags per block suffice to tolerate realistic missing-call rates.

## Sources

- Y.-T. Huang, K. Zhang, T. Chen, K.-M. Chao, "Selecting additional tag SNPs for tolerating missing data in genotyping", BMC Bioinformatics 6 (2005) 263, Methods, problem MRTS, Lemmas 1–5 and Theorems 1–5, <https://doi.org/10.1186/1471-2105-6-263>, PMCID PMC1316880.
