---
article_id: af_f36cfae071a9857ccc108872
declaration: theorem
origin: cited
statement: formalized
lean: FrequencyDecomposition.main_lemma_real
---

# Lemma (Main lemma in real)

Let $\mathcal{T}$ be a set of $1 \times R$ rectangles in $\mathbb{R}^2$. Let $f = \sum_{T \in \mathcal{T}} \phi_T(x)$. Then $$f = \sum_{\substack{1 \leq r \leq R \\ \text{dyadic}}} f_r(x)$$ such that $\operatorname{supp} \hat{f}_r \subseteq B(1/r)$ and $\|f_r\|_2^2 \lesssim N_{\mathcal{T}}(r) |\mathcal{T}| r^{-1} R$ where $N_{\mathcal{T}}(r) \coloneqq \max_{\tilde{T} \colon 2r \times 2R \text{ rect}} \#\{T \in \mathcal{T} \mid T \subset \tilde{T}\}$.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Lemma (Orthogonality)](019-orthogonality.md)

## Sources

- [MIT 18.156 Projection Theory (Spring 2025), Section: Fourier Method](../../../../../sources/v1/ProjectionTheory.md)
