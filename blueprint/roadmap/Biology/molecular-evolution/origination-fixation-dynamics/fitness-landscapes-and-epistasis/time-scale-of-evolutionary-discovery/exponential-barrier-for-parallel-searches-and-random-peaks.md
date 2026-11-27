# Exponential barrier for parallel searches and randomly placed peaks

Work in the origination–fixation model of evolution on sequences of length $L$ over a four-letter alphabet, with broad peaks of target sequences in an otherwise flat landscape.

**Theorem (independent searches).** In every case where the expected discovery time of a single search has an exponential lower bound, for all polynomials $p_1(\cdot)$, $p_2(\cdot)$ and $p_3(\cdot)$ and for any starting sequence at Hamming distance at least $3L/4$ from the target center, the probability that any one of $p_3(L)$ independent searches reaches the target set within $p_1(L)$ steps is at most $1/p_2(L)$.

Informally, if the expected discovery time of a single search is $d$, then $M$ independent searches started far from the target all fail for $\beta$ steps with probability at least $\exp(-M\beta/d)$. For instance, $10^{24}$ independent populations of size $N = 10^6$, run for $10^{14}$ generations on a sequence of length $L = 1000$ with peak width $c = 1/2$, succeed with probability below $10^{-26}$. Many mutant lineages evolving in parallel within one population behave like such independent searches, so they do not help either.

**Theorem (randomly placed peaks).** Consider a single search on a landscape with $m \ll 4^L$ target centers chosen uniformly at random, each with a broad peak of width at most $c$, where $c < 3/4$. Then with high probability the expected discovery time of the target set is at least

$$\frac{1}{m}\,\exp\!\left[2L\left(\tfrac{3}{4} - c\right)^2\right].$$

Whether this bound is exponential depends on how $m$ grows with $L$, and even exponentially many randomly placed peaks need not give polynomial discovery time. Recombination shortens discovery times by at most a factor linear in $L$, which cannot turn an exponential time into a polynomial one. Polynomial time is recovered only when starting sequences a bounded number $k$ of mutations from the target are regenerated over and over (for example by gene duplication); then $L^{k+1}$ searches suffice with high probability, even under neutral drift.

## Depends on

- [Polynomial–exponential dichotomy for discovering a broad peak](polynomial-exponential-dichotomy-for-discovering-a-broad-peak.md)

## Proof depends on

- [Hoeffding's inequality for averages of bounded variables](../../../../../Probability/concentration-inequalities/hoeffding-s-inequality/measure-real-avg-sub-ge-le.md)
- [Countable subadditivity of a measure](../../../../../MeasureTheory/measures/measures-and-countable-additivity/measures/measure-i-union-le.md)

## Expansion

Parallel searches: if the expected discovery time of one search is exponential, the probability that it succeeds within polynomially many steps is negligible, and independence makes the probability that all searches fail the product of the individual failure probabilities. Random peaks: without selection the walk on all $4^L$ sequences moves to each of the $3L$ neighbors with probability $1/(3L)$ per mutation and mixes in $O(L\log L)$ steps to the uniform distribution. By the single-peak lower bound and a union bound over the $m$ centers, the target is reached within the first $O(L\log L)$ steps with negligible probability. After mixing, each step is essentially a uniform draw from sequence space, and Hoeffding's inequality bounds the fraction of sequences within distance $cL$ of any center, so on the order of $\exp(2(3/4 - c)^2 L)/m$ steps are needed before a target sequence is found.

## Sources

- K. Chatterjee, A. Pavlogiannis, B. Adlam, M. A. Nowak, "The time scale of evolutionary innovation", PLoS Computational Biology 10(9) (2014) e1003818, Theorems 2–3 and Materials and Methods (detailed proofs in Text S1, Theorems S5–S6 and Sections 8–10), <https://doi.org/10.1371/journal.pcbi.1003818> (PMC4161296).
