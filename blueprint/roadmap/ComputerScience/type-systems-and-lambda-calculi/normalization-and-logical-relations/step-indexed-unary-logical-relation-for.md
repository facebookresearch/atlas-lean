# Step-indexed unary logical relation for recursive types

For the simply typed lambda calculus with iso-recursive types under call-by-value, define step-indexed value and expression relations $\mathcal{V}_k[A]$ and $\mathcal{E}_k[A]$ by well-founded recursion on $(k, A)$, with $\mathrm{fold}\ v \in \mathcal{V}_k[\mu\alpha.A]$ when $v \in \mathcal{V}_j[A[\mu\alpha.A/\alpha]]$ for all $j < k$. The fundamental lemma holds: every well-typed term, under any closing substitution of related values, is in $\mathcal{E}_k[A]$ for every $k$. As a corollary, well-typed closed terms never get stuck (semantic type safety).

## Proof depends on

- [Iso-recursive types: safety without normalization](../advanced-type-systems/iso-recursive-types-safety-without-normalization.md)

## Sources

- A. Ahmed, "Step-indexed syntactic logical relations for recursive and quantified types", *ESOP 2006*, LNCS 3924, Springer, 2006
- A. W. Appel and D. McAllester, "An indexed model of recursive types for foundational proof-carrying code", *ACM Transactions on Programming Languages and Systems* 23(5):657–683, 2001
