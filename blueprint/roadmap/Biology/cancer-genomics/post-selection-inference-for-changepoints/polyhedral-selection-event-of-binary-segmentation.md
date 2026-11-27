# Binary segmentation selects a polyhedral cone of data vectors

Let $y \in \mathbb{R}^n$ be a data vector (for example log copy-number ratios along a chromosome). For $1 \le s \le b < e \le n$ define the **CUSUM contrast** $g_{(s,b,e)} \in \mathbb{R}^n$ by

$$g_{(s,b,e)}^{\top} y = \sqrt{\frac{1}{\frac{1}{e - b} + \frac{1}{b + 1 - s}}}\; \big( \bar y_{(b+1):e} - \bar y_{s:b} \big), \qquad \bar y_{a:c} = \frac{1}{c - a + 1} \sum_{i=a}^{c} y_i .$$

The **$k$-step binary segmentation** (BS) algorithm, for $1 \le k \le n - 1$, works as follows. At step $\ell = 1, \dots, k$, let $\hat b_1, \dots, \hat b_{\ell-1}$ be the changepoints found so far and let $I_1, \dots, I_{\ell}$ be the induced partition of $\{1, \dots, n\}$ into intervals $I_j = \{s_j, \dots, e_j\}$ (a changepoint $b$ ends an interval at $b$), discarding intervals of length one. Choose

$$(\hat j_\ell, \hat b_\ell) \in \operatorname*{argmax}_{j,\; b \in \{s_j, \dots, e_j - 1\}} \big| g_{(s_j, b, e_j)}^{\top} y \big|, \qquad \hat d_\ell = \operatorname{sign}\big( g_{(s_{\hat j_\ell}, \hat b_\ell, e_{\hat j_\ell})}^{\top} y \big),$$

with any fixed rule for breaking ties in the argmax and any fixed value of $\operatorname{sign}(0) \in \{-1, +1\}$. Its selected model is $M^{\mathrm{BS}}_{1:k}(y) = \{\hat b_{1:k}(y), \hat d_{1:k}(y)\}$, the ordered history of locations and directions.

Call locations $b_{1:k}$ **feasible** if they are distinct elements of $\{1, \dots, n - 1\}$; then at each step $\ell$ the location $b_\ell$ is a split point of exactly one interval $I_{j_\ell} = \{s_{j_\ell}, \dots, e_{j_\ell}\}$ of the partition induced by $b_{1:\ell-1}$, and there are $n - \ell$ candidate pairs $(j, b)$ at that step, of which $n - \ell - 1$ compete with $(j_\ell, b_\ell)$. For infeasible locations the selection event is empty.

**Proposition (Hyun, Lin, G'Sell and Tibshirani 2021, Proposition 1).** For any fixed $k$ with $1 \le k \le n - 1$, feasible locations $b_{1:k}$ and directions $d_{1:k} \in \{-1, +1\}^k$, there is an explicitly constructible matrix $\Gamma$ with $\sum_{\ell=1}^{k} \bigl(2(n - \ell - 1) + 1\bigr)$ rows, none of them zero, such that

$$\{ y : \Gamma y > 0 \} \subseteq \{ y \in \mathbb{R}^n : M^{\mathrm{BS}}_{1:k}(y) = \{b_{1:k}, d_{1:k}\} \} \subseteq \{ y : \Gamma y \ge 0 \}$$

(componentwise inequalities), whatever the tie-breaking rule. In particular the selection event equals the convex polyhedral cone $\{ y : \Gamma y \ge 0 \}$ up to a Lebesgue-null set (a subset of finitely many hyperplanes $\{\gamma^{\top} y = 0\}$, one for each row $\gamma$ of $\Gamma$). Analogous statements hold, with other row counts, for circular binary segmentation and the fused lasso path. For **wild binary segmentation** the single-cone statement needs a larger selection record: §3.1.2, Proposition 2, conditions on the set of sampled intervals and records the winning interval at each step in addition to the changepoints and directions; conditioning on changepoints and directions alone can give a union of such cones.

## Expansion

Write $g_\ell = g_{(s_{j_\ell}, b_\ell, e_{j_\ell})}$ for the winning contrast at step $\ell$, computed from the partition induced by $b_{1:\ell-1}$. Step $\ell$ contributes the sign row and, for every competitor $(s_j, b, e_j)$, two comparison rows:

$$d_\ell\, g_\ell^{\top} y \ge 0, \qquad d_\ell\, g_\ell^{\top} y \ge g_{(s_j, b, e_j)}^{\top} y, \qquad d_\ell\, g_\ell^{\top} y \ge -g_{(s_j, b, e_j)}^{\top} y,$$

since $|t| \le c$ is the pair $t \le c$, $-t \le c$. When there is at least one competitor the sign row is implied by the comparison rows, but when $n - \ell = 1$ there is no competitor and the sign row alone records $\hat d_\ell = d_\ell$ (for $n = 2$, $k = 1$ and $d_1 = +1$ the event is $\{y_2 \ge y_1\}$ up to the tie $y_1 = y_2$, not all of $\mathbb{R}^2$). If $M^{\mathrm{BS}}_{1:k}(y) = \{b_{1:k}, d_{1:k}\}$, the partitions along the run are those induced by $b_{1:k}$, so every row holds with $\ge$. Conversely, if every row holds strictly, then at each step the winning pair is the unique maximizer and its CUSUM has sign $d_\ell$, so by induction on $\ell$ the algorithm reproduces $b_{1:k}$ and $d_{1:k}$ regardless of the tie-breaking rule. No row is the zero vector: distinct CUSUM contrasts are not parallel, and $g_\ell \ne 0$. Stacking the rows over $\ell = 1, \dots, k$ gives $\Gamma$.

## Sources

- S. Hyun, K. Z. Lin, M. G'Sell and R. J. Tibshirani, "Post-selection inference for changepoint detection algorithms with application to copy number variation data", Biometrics 77 (2021), 1037–1049, <https://doi.org/10.1111/biom.13422>. Numbering of the published journal edition: Section 2.1.1 (CUSUM statistic, Eq. 3), Section 2.1.2 (wild binary segmentation), Section 3.1.1 (Proposition 1, binary segmentation) and Section 3.1.2 (Proposition 2, wild binary segmentation).
