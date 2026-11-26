# The Hennessy–Milner theorem

Let $P$ be a set of processes and $(R_i)_{i \in I}$ a family of binary relations on $P$, the observation relations; $(p, p') \in R_i$ is an $i$-experiment on $p$. If every $R_i$ is image-finite, then two processes are [observationally equivalent](observational-equivalence-by-stratification.md) if and only if they satisfy the same formulas of [Hennessy–Milner logic](hennessy-milner-logic.md):

$$p \sim q \iff \mathcal{L}(p) = \mathcal{L}(q).$$

By the [maximal fixed point characterization](observational-equivalence-is-the-maximal-fixed-point.md), for image-finite systems the left-hand side is strong bisimilarity.

## Depends on

- [Observational equivalence by stratification](observational-equivalence-by-stratification.md)
- [Hennessy–Milner logic](hennessy-milner-logic.md)
- [Observational equivalence is the maximal fixed point for image-finite systems](observational-equivalence-is-the-maximal-fixed-point.md)

## Sources

- M. Hennessy and R. Milner, "Algebraic laws for nondeterminism and concurrency", *Journal of the ACM* 32(1):137–161, 1985, <https://www.scss.tcd.ie/matthew.hennessy/pubs/old/HMjacm85.pdf>, Section 2.2, Theorem 2.2; the proof, by induction on $n$ for $\sim_n$ and on formulas, is in Appendix A.
- The CSLib contributors, *cslib* at revision 22b39634, `Cslib.Logic.Modal.theoryEq_eq_bisimilarity`, <https://github.com/leanprover/cslib/blob/22b39634cb3dc80d829683ad1f65c5680b722309/Cslib/Logics/HML/Basic.lean#L184-L187>: for an image-finite labelled transition system, two states satisfy the same Hennessy–Milner formulas exactly when they are bisimilar. With no atomic propositions its hypothesis on the valuation holds vacuously, and composed with the [maximal fixed point characterization](observational-equivalence-is-the-maximal-fixed-point.md) it gives this page's statement.
