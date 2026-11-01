---
article_id: af_894fa99525cacb7e40899e70
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: DedekindKummer.dedekind_kummer
---

# Theorem 6.14 (Dedekind-Kummer)

Assume $AKLB$ with $L=K(\alpha)$ and $\alpha \in B$. Let $f \in A[x]$ be the minimal polynomial of $\alpha$, let $\mathfrak{p}$ be a prime of $A$, and let $\bar{f}=\bar{g}_{1}^{e_{1}} \cdots \bar{g}_{r}^{e_{r}}$ be its factorization into monic irreducibles in $(A/\mathfrak{p})[x]$. Let $\mathfrak{q}_{i}\coloneqq (\mathfrak{p}, g_{i}(\alpha))$, where $g_{i} \in A[x]$ is any lift of $\bar{g}_{i}$ in $(A/\mathfrak{p})[x]$ under the reduction map $A[x] \rightarrow (A/\mathfrak{p})[x]$. If $B=A[\alpha]$ then $\mathfrak{p} B=\mathfrak{q}_{1}^{e_{1}} \cdots \mathfrak{q}_{r}^{e_{r}}$ is the prime factorization of $\mathfrak{p} B$ in $B$ and the residue field degree of $\mathfrak{q}_{i}$ is $\operatorname{deg} \bar{g}_{i}$.

## Depends on

- [Definition 1.19](../../section-1/section-1-6/015-definition-1-19.md)
- [Definition 2.10](../../section-2/027-definition-2-10.md)
- [Corollary 3.13](../../section-3/048-corollary-3-13.md)
- [Definition 4.3](../../section-4/section-4-1/part-01/058-definition-4-3.md)
- [Definition 5.29](../../section-5/section-5-3/118-definition-5-29.md)

## Proof depends on

- [Theorem 5.35](../../section-5/section-5/122-theorem-5-35.md)
- [Proposition 6.7](../section-6-2/130-proposition-6-7.md)
- [Theorem 6.10](../section-6-2/133-theorem-6-10.md)

## Sources

- [MIT 18.785 Number Theory I (Fall 2021), Section 6.5](../../../../../../sources/v1/NumberTheoryI.md)
