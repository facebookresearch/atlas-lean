---
article_id: af_7ec52453e427e56093cf17c9
declaration: theorem
origin: cited
lean: BooleanFourier.friedgut_l2_bridge
---

# Theorem 3.1

For all $t, \varepsilon, \delta > 0$ there exists an algorithm whose runtime is $\operatorname{poly}(n, t, 1/\varepsilon, 1/\delta)$ such that the following holds. Given an oracle access to a $(t, \varepsilon)$-sparse function $f \colon \{-1, 1\}^n \to \{-1, 1\}$, the algorithm produces a hypothesis function $H \colon \{-1, 1\}^n \to \{-1, 1\}$ such that $\|f - H\|_2^2 \leqslant 4\varepsilon + \delta$.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Definition 0.1](../lecture-5/027-definition-0-1.md)
- [Claim 2.1 (Lecture 3, Section 2)](001-claim-2-1.md)
- [Claim 2.2 (Lecture 1, Section 2.1)](../lecture-1/002-claim-2-2.md)
- [Claim 1.2](016-claim-1-2.md)

## Sources

- [MIT 18.218 Analysis of Boolean Functions (Spring 2021), Lecture 3, Section 3](../../../../sources/v1/BooleanFunctions.md)
