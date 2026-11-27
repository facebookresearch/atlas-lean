# Trajectory likelihood conditioned on segregation in the final sample

**Setting.** In the discrete Wright–Fisher epoch model with forward variables $v_{k,i} = \Pr(O_{[1:k]} = o_{[1:k]}, C_{t_k} = i)$, let $S_K$ be the event that allele $A$ is segregating in the final sample ($1 \le O_K < n_K$) and $F_K$ the event that it is segregating or fixed ($1 \le O_K \le n_K$). Such conditioning models data sets ascertained to contain only loci polymorphic (or present) at the last sampling time.

**Proposition.**

$$\Pr\big(O_{[1:K]} = o_{[1:K]} \mid S_K\big) = \frac{\Pr(S_K \mid O_K = o_K)}{\Pr(S_K)} \sum_{i=0}^{2N_{t_K}} v_{K,i},$$

where $\Pr(S_K \mid O_K = o_K) = 1$ if $1 \le o_K < n_K$ and $0$ otherwise, and $\Pr(S_K)$ is the model probability that a sample of size $n_K$ at $t_K$ is polymorphic. The same formula with $F_K$ in place of $S_K$ (indicator $1 \le o_K \le n_K$) gives the likelihood conditioned on segregation or fixation.

## Depends on

- [Wright–Fisher forward recursion for allele counts under piecewise-constant size](wright-fisher-forward-recursion-under-piecewise-constant-size.md)

## Proof depends on

Its proof consists of the steps listed under Expansion.

## Expansion

By Bayes' rule, $\Pr(O = o \mid S_K) = \Pr(S_K \mid O = o)\Pr(O = o)/\Pr(S_K)$, and $S_K$ is a function of $O_K$ alone, so the first factor is an indicator. The denominator is computed by propagating the initial distribution to $t_K$ and summing binomial sampling probabilities of a polymorphic sample. Ignoring this ascertainment biases selection estimates, since trajectories that lost the allele are excluded from the data but not from the unconditioned likelihood.

## Sources

- E. M. Jewett, M. Steinrücken, Y. S. Song, "The effects of population size histories on estimates of selection coefficients from time-series genetic data", Molecular Biology and Evolution 33(11) (2016) 3002–3027, Methods (conditional probabilities), Eqs (20)–(21) and Appendix C, <https://doi.org/10.1093/molbev/msw173>, PMCID PMC5062326.
