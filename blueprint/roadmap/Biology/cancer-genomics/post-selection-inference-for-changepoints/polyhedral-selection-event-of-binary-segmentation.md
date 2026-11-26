# Binary segmentation selects a polyhedral cone of data vectors

Let $y \in \mathbb{R}^n$ be a data vector (for example log copy-number ratios along a chromosome). For $1 \le s \le b < e \le n$ define the **CUSUM contrast** $g_{(s,b,e)} \in \mathbb{R}^n$ by

$$g_{(s,b,e)}^{\top} y = \sqrt{\frac{1}{\frac{1}{e - b} + \frac{1}{b + 1 - s}}}\; \big( \bar y_{(b+1):e} - \bar y_{s:b} \big), \qquad \bar y_{a:c} = \frac{1}{c - a + 1} \sum_{i=a}^{c} y_i .$$

The **$k$-step binary segmentation** (BS) algorithm works as follows. At step $\ell = 1, \dots, k$, let $\hat b_1, \dots, \hat b_{\ell-1}$ be the changepoints found so far and let $I_1, \dots, I_{\ell}$ be the induced partition of $\{1, \dots, n\}$ into intervals $I_j = \{s_j, \dots, e_j\}$, discarding intervals of length one. Choose

$$(\hat j_\ell, \hat b_\ell) \in \operatorname*{argmax}_{j,\; b \in \{s_j, \dots, e_j - 1\}} \big| g_{(s_j, b, e_j)}^{\top} y \big|, \qquad \hat d_\ell = \operatorname{sign}\big( g_{(s_{\hat j_\ell}, \hat b_\ell, e_{\hat j_\ell})}^{\top} y \big).$$

Its selected model is $M^{\mathrm{BS}}_{1:k}(y) = \{\hat b_{1:k}(y), \hat d_{1:k}(y)\}$.

**Proposition (Hyun, Lin, G'Sell and Tibshirani 2021, Proposition 1).** For any fixed $k \ge 1$, locations $b_{1:k}$ and directions $d_{1:k} \in \{-1, +1\}^k$, there is an explicitly constructible matrix $\Gamma$ with $2 \sum_{\ell=1}^{k} (n - \ell - 1)$ rows such that

$$\{ y \in \mathbb{R}^n : M^{\mathrm{BS}}_{1:k}(y) = \{b_{1:k}, d_{1:k}\} \} = \{ y : \Gamma y \ge 0 \}$$

(componentwise inequality). In particular the selection event is a convex polyhedral cone. The same holds, with other row counts, for wild binary segmentation, circular binary segmentation and the fused lasso path.

## Expansion

For $k = 1$, the event that $b_1$ with sign $d_1$ wins is equivalent to the $2(n - 2)$ linear inequalities

$$d_1\, g_{(1, b_1, n)}^{\top} y \ge g_{(1, b, n)}^{\top} y \quad \text{and} \quad d_1\, g_{(1, b_1, n)}^{\top} y \ge -g_{(1, b, n)}^{\top} y, \qquad b \in \{1, \dots, n-1\} \setminus \{b_1\},$$

since $|t| \le c$ is the pair $t \le c$, $-t \le c$, and $d_1 g^{\top} y = |g^{\top} y|$ fixes the sign. Given the first $\ell - 1$ selections, the partition is fixed, so step $\ell$ adds $2(n - \ell - 1)$ further inequalities of the same form comparing the winning CUSUM with every competitor in every current interval. Stacking these rows gives $\Gamma$ by induction.

## Sources

- S. Hyun, K. Z. Lin, M. G'Sell and R. J. Tibshirani, "Post-selection inference for changepoint detection algorithms with application to copy number variation data", Biometrics 77 (2021), 1037–1049, Section 2.1 (Eq. 4) and Section 3.1 (Proposition 1), <https://doi.org/10.1111/biom.13422>.
