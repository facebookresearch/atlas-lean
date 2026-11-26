# The Hennessy–Milner theorem

Let $P$ be a set of processes and $(R_i)_{i \in I}$ a family of binary relations on $P$, the observation relations; $(p, p') \in R_i$ is an $i$-experiment on $p$. If every $R_i$ is image-finite, then two processes are [observationally equivalent](observational-equivalence-by-stratification.md) if and only if they satisfy the same formulas of [Hennessy–Milner logic](hennessy-milner-logic.md):

$$p \sim q \iff \mathcal{L}(p) = \mathcal{L}(q).$$

By the [maximal fixed point characterization](observational-equivalence-is-the-maximal-fixed-point.md), for image-finite systems the left-hand side is strong bisimilarity.

## Depends on

- [Observational equivalence by stratification](observational-equivalence-by-stratification.md)
- [Hennessy–Milner logic](hennessy-milner-logic.md)

## Proof depends on

- [Observational equivalence by stratification](observational-equivalence-by-stratification.md)
- [Hennessy–Milner logic](hennessy-milner-logic.md)

## Sources

- M. Hennessy and R. Milner, "Algebraic laws for nondeterminism and concurrency", *Journal of the ACM* 32(1):137–161, 1985, <https://www.scss.tcd.ie/matthew.hennessy/pubs/old/HMjacm85.pdf>, Section 2.2, Theorem 2.2; the proof, by induction on $n$ for $\sim_n$ and on formulas, is in Appendix A.
