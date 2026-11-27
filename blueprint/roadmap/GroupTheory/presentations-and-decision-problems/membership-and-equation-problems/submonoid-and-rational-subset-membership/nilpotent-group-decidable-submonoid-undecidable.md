# A nilpotent group with decidable submonoid membership but undecidable rational subset membership

There are integers $m, n \ge 0$ such that the group $N_{2,m} \times \mathbb{Z}^n$, with $N_{2,m}$ the free nilpotent group of class 2 on $m$ generators, has decidable submonoid membership problem and undecidable rational subset membership problem.

For $m \ge 0$ let $N_{2,m}$ be the free nilpotent group of class 2 (the free 2-step nilpotent group) of rank $m$, the quotient of the free group on $m$ generators by the third term of its lower central series. There exist $m, n \ge 0$ such that the finitely generated nilpotent group $N_{2,m} \times \mathbb{Z}^n$ has decidable submonoid membership problem and undecidable rational subset membership problem (the corollary at the end of the section "Dimension gain for the Submonoid Membership" of the source).

So for finitely generated nilpotent groups the two problems are not equivalent.

## Depends on

- [Submonoid membership problem](submonoid-membership-problem.md)
- [Rational subset membership problem](rational-subset-membership-problem.md)
- [Group](../../../group-basics/group.md)

## Proof depends on

None.

## Expansion

Earlier work on knapsack problems in nilpotent groups, cited by the source, shows that some group $N_{2,m} \times \mathbb{Z}^n$ has undecidable rational subset membership problem, and a later result cited there gives such a group with $m \le 26$. Take such a group with $m$ minimal. The source's dimension-gain theorem reduces each instance of the submonoid membership problem of $G = N_{2,m} \times \mathbb{Z}^n$ to finitely many instances of rational subset membership in subgroups $H$ with smaller Hirsch length of $[H, H]$. Each such subgroup has a finite-index subgroup isomorphic to $N_{2,k} \times \mathbb{Z}^\ell$ with $k < m$, computable from generators, and rational subset membership there is decidable by minimality of $m$; decidability passes to $H$ through finite-index subgroups.

## Sources

- C. Bodart, "Membership problems in nilpotent groups", Journal of Groups, Complexity, Cryptology 17 (2025), no. 1, article 13954, https://doi.org/10.46298/jgcc.2025.17.1.13954; arXiv:2401.15504v6 (the corollary closing the section "Dimension gain for the Submonoid Membership" in arXiv:2401.15504v6, proved from the dimension-gain theorem and the lemma on subgroups of $N_{2,m} \times \mathbb{Z}^n$ in the same section).
