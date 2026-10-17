---
article_id: af_3bf3b6faaff0cc83c3a40402
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: continuity_of_roots
---

# Theorem 11.19 (Continuity of roots)

Let $K$ be the fraction field of a complete DVR and $f \in K[x]$ a monic irreducible separable polynomial. There exists $\delta=\delta(f) \in \mathbb{R}_{>0}$ such that for every monic polynomial $g \in K[x]$ with $\|f-g\|_1\lt \delta$ the following holds: Every root $\beta$ of $g$ belongs to a root $\alpha$ of $f$ for which $K(\beta)=K(\alpha)$. In particular, every such $g$ is separable, irreducible, and has the same splitting field as $f$.

## Depends on

- [Definition 11.14](230-definition-11-14.md)
- [Definition 11.17](232-definition-11-17.md)
- [Definition 1.10](../section-1/section-1-4/008-definition-1-10.md)
- [Definition 4.1](../section-4/section-4-1/part-01/057-definition-4-1.md)
- [Definition 8.1](../section-8/172-definition-8-1.md)

## Proof depends on

- [Lemma 11.18](233-lemma-11-18.md)
- [Lemma 11.15 (Krasner's lemma)](231-krasner-s-lemma.md)

## Sources

- [MIT 18.785 Number Theory I (Fall 2021), Section 11.2](../../../../../sources/v1/NumberTheoryI.md)
