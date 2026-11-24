# Convergence of Cannings ancestral partition chains for a fixed sample size

Fix $n \ge 2$ and assume the pattern-limit hypothesis of [the generator convergence lemma](generator-convergence-of-cannings-partition-chai.md), with limiting rate matrix $Q_n$ on the partitions of $[n]$. Then the one-generation transition matrices $\Pi_N$ of the ancestral partition chain satisfy

$$\Pi_N^{\lfloor t / c_N \rfloor} \to e^{t Q_n} \qquad \text{for every } t \ge 0,$$

and the finite-dimensional distributions of the chain run at time scale $1/c_N$ from the partition into singletons converge to those of the continuous-time Markov chain with rate matrix $Q_n$. The statement is for a fixed sample size and finite-dimensional distributions only; it makes no claim in path space.

The raw-moment hypothesis of Möhle and Sagitov, together with the transform from its limits to merger rates, is the hypothesis of [the classification programme](mohle-sagitov-classification-limiting-merger-rat.md).

## Depends on

- [Generator convergence of Cannings ancestral partition chains under pattern limits](generator-convergence-of-cannings-partition-chai.md)

## Expansion

1. The matrix limit from the generator limit, by $(I + c_N A_N)^{\lfloor t/c_N \rfloor} \to e^{tA}$ when $A_N \to A$.
2. The finite-dimensional distributions from the matrix limit and the Markov property.
3. Checks against the existing special cases: in the Λ case it reproduces the [Möhle–Sagitov limit of the lineage count](tendsto-lineage-matrix-pow.md), in the Kingman case the [convergence of transition matrices to Kingman's](../kingman-limit-of-cannings-models/tendsto-ancestral-matrix-pow.md), and the sweepstake model has the rates of $\Lambda = \delta_1$.

## Sources

- M. Möhle and S. Sagitov, A classification of coalescent processes for haploid exchangeable population models, *Ann. Probab.* 29 (2001), 1547–1562, <https://doi.org/10.1214/aop/1015345761> (classification).
