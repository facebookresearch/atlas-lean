# Closed-form scores for the categorical colocalization prior

Let $p_1, p_2, p_{12}$ be [colocalization prior parameters](coloc-prior.md) on a finite set $\iota$ of variants, with [null mass](p0.md) $p_0$, and let $\mathrm{BF}^{(1)}, \mathrm{BF}^{(2)} : \iota \to \mathbb{R}$ be arbitrary. The categorical closed-form scores of the five [colocalization hypotheses](coloc-hypothesis.md) are

- $C_{\mathrm{cat}}(H_0) = p_0$;
- $C_{\mathrm{cat}}(H_1) = p_1 \sum_j \mathrm{BF}^{(1)}_j$;
- $C_{\mathrm{cat}}(H_2) = p_2 \sum_k \mathrm{BF}^{(2)}_k$;
- $C_{\mathrm{cat}}(H_3) = p_1 p_2 \bigl(\sum_j \mathrm{BF}^{(1)}_j \sum_k \mathrm{BF}^{(2)}_k - \sum_j \mathrm{BF}^{(1)}_j \mathrm{BF}^{(2)}_j\bigr)$;
- $C_{\mathrm{cat}}(H_4) = p_{12} \sum_j \mathrm{BF}^{(1)}_j \mathrm{BF}^{(2)}_j$,

all sums over $\iota$. They differ from the [closed-form scores](coloc-closed-form.md) only in the $H_0$ score $p_0$ instead of $1$.
