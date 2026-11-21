# Low-rank adaptation (LoRA)

For a frozen pretrained weight matrix $W_0 \in \mathbb{R}^{d \times k}$ and a rank $r$,
low-rank adaptation trains $B \in \mathbb{R}^{d \times r}$ and $A \in \mathbb{R}^{r \times k}$ and
uses the weight $W_0 + BA$: a layer input $x$ gives $h = W_0 x + BAx$. The matrix $A$ is
initialised at random and $B$ at zero, so the update $BA$ starts at $0$.

Only the update is low rank: $BA$ factors through $\mathbb{R}^r$, so
$\operatorname{rank}(BA) \le r$. The merged weight $W_0 + BA$, which can replace $W_0$ at
inference, is generally not low rank.

The method computes no singular value decomposition. Singular vectors appear only in the paper's
analysis of trained updates. PiSSA uses the opposite letters: its $A$ has $r$ columns and its $B$
has $r$ rows.

## Informally uses

- [Rank of a product of matrices](../../../LinearAlgebra/linear-maps-and-duality/rank-of-a-product.md):
  mathematical prerequisite, the bound $\operatorname{rank}(BA) \le r$.

## Sources

- E. J. Hu, Y. Shen, P. Wallis, Z. Allen-Zhu, Y. Li, S. Wang, L. Wang and W. Chen, "LoRA: Low-Rank Adaptation of Large Language Models", arXiv:2106.09685 (version 2), Section 4.1, equation (3) (the update, its initialisation and merging), and Sections 7.2–7.3 and Appendices G–H (the analysis with singular vectors).
