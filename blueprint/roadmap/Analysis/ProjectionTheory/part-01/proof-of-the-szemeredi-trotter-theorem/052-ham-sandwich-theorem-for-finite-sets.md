---
article_id: af_b42ff2bd63cc7d9e20084dea
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: HamSandwich.ham_sandwich_finite
---

# Lemma (Ham Sandwich theorem for finite sets)

Let $s_1, s_2, \ldots, s_N$ be a set of finite sets in $\mathbb{R}^n$. Then there exists a polynomial level set such that for every $s_i$, $|s_i \cap \{x \mid p(x) > 0\}| \leq \frac{|s_i|}{2}$ and $|s_i \cap \{x \mid p(x) < 0\}| \leq \frac{|s_i|}{2}$.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Theorem (Polynomial Ham Sandwich Theorem)](051-polynomial-ham-sandwich-theorem.md)

## Sources

- [MIT 18.156 Projection Theory (Spring 2025), Proof of the Szemeredi-Trotter theorem](../../../../../sources/v1/ProjectionTheory.md)
