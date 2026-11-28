# Observational equivalence is the maximal fixed point for image-finite systems

Let $P$ be a set of processes and $(R_i)_{i \in I}$ a family of binary relations on $P$, the observation relations; $(p, p') \in R_i$ is an $i$-experiment on $p$. If every $R_i$ is image-finite, then [observational equivalence](observational-equivalence-by-stratification.md) $\sim$ is the maximum solution of $S = E(S)$. Since $E$ is monotone on the complete lattice of relations, its maximum fixed point is also the largest $S$ with $S \subseteq E(S)$, so for image-finite systems $\sim$ is strong bisimilarity with respect to the relations $R_i$.

## Depends on

- [Observational equivalence by stratification](observational-equivalence-by-stratification.md)

## Sources

- M. Hennessy and R. Milner, "Algebraic laws for nondeterminism and concurrency", *Journal of the ACM* 32(1):137–161, 1985, <https://www.scss.tcd.ie/matthew.hennessy/pubs/old/HMjacm85.pdf>, Section 2.1, Theorem 2.1, with the observation that image-finiteness makes $E$ anticontinuous; the proof is in Appendix A.
- The CSLib contributors, *cslib* at revision 22b39634, `Cslib.LTS.bisimulationStep_gfp` and `Cslib.LTS.BisimilarityApprox.omega_eq_bisimilarity`, <https://github.com/leanprover/cslib/blob/22b39634cb3dc80d829683ad1f65c5680b722309/Cslib/Foundations/Semantics/LTS/Bisimulation.lean#L312> and <https://github.com/leanprover/cslib/blob/22b39634cb3dc80d829683ad1f65c5680b722309/Cslib/Foundations/Semantics/LTS/Bisimulation.lean#L604-L606>. For the labelled transition system with a transition from $p$ to $p'$ labelled $i$ whenever $(p, p') \in R_i$, `bisimulationStep` is the map $E$ and the approximant at $\omega$ is the intersection of the iterates of $E$ from the universal relation. The first theorem identifies the greatest fixed point of $E$ with bisimilarity; the second identifies the approximant at $\omega$ with bisimilarity when every $R_i$ is image-finite. Together they give this page's statement.
