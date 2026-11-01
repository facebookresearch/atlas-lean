---
article_id: af_c7d91323727c1015d895debc
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: LpSpaces.memLp_iff_iSup_lintegral_Icc_inter_lt_top
---

# Proposition (Characterization of $L^p$ membership)

Let $E \subset \mathbb{R}$ be measurable. Then $f \in L^p(E)$ if and only if (letting $n$ range over positive integers) $\lim_{n \to \infty} \int_{[-n, n] \cap E} |f|^p < \infty$.

## Depends on

- [Definition ($L^p$ space)](045-l-p-space.md)

## Proof depends on

- [Theorem (Monotone Convergence Theorem)](../march-30/028-monotone-convergence-theorem.md)

## Sources

- [MIT 18.102 Introduction to Functional Analysis (Spring 2021), April 6, 2021 section](../../../../../sources/v1/IntroductionToFunctionalAnalysis.md)
