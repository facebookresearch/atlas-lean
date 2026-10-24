---
article_id: af_b6fbc86e351992467bf05232
declaration: theorem
origin: cited
statement: formalized
lean: RiemannStieltjes.corollary_18_28
---

# Corollary 18.28

Let $f$ and $g$ be functions on $[a, b]$ such that $f$ and $g$ are not both discontinuous from the left or from the right at integers $n \in [a, b]$, and let $G(x) = \sum_{a < n \leq x} g(n)$. Then $\sum_{a < n \leq b} f(n) g(n) = \int_{a}^{b} f(x)\,dG(x)$. In particular, the integral on the RHS always exists.

## Depends on

- [Definition 18.23](369-definition-18-23.md)

## Sources

- [MIT 18.785 Number Theory I (Fall 2021), Section 18.5](../../../../../../sources/v1/NumberTheoryI.md)
