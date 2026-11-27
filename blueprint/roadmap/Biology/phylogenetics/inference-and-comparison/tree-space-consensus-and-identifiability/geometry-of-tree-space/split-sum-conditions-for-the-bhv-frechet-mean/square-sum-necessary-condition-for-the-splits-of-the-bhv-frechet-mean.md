# Square-sum necessary condition for the splits of the BHV Fréchet mean

**Setting.** As for the split-sum condition: a sample $\mathcal T=\{T_1,\dots,T_r\}$ in BHV tree space $\mathbb T_n$, weights $|x|_T$, sample split set $E(\mathcal T)$, and $X(S)$ the splits incompatible with at least one split of $S$.

**Definition.** For a set of splits $S\subseteq E(\mathcal T)$, the *square-sum difference* is

$$\mathrm{ssd}(S,\mathcal T)=\sum_{s\in S}\Big(\sum_{T\in\mathcal T}|s|_T\Big)^2-\sum_{x\in E(\mathcal T)\cap X(S)}\ \sum_{T\in\mathcal T}|x|_T^2 .$$

**Theorem.** Let $\mu$ be the Fréchet mean of $\mathcal T$ and $S=\{s_1,\dots,s_m\}$ its splits of positive weight, and suppose $S$ is nonempty ($m\ge1$, that is, $\mu$ is not the star tree). Then $\mathrm{ssd}(S,\mathcal T)>0$, that is

$$\sum_{i=1}^m\Big(\sum_{T\in\mathcal T}|s_i|_T\Big)^2>\sum_{x\in E(\mathcal T)\cap X(\mu)}\ \sum_{T\in\mathcal T}|x|_T^2 .$$

Consequently, by Cauchy–Schwarz,

$$r\sum_{i=1}^m\sum_{T}|s_i|_T^2>\sum_{x\in E(\mathcal T)\cap X(\mu)}\sum_T|x|_T^2,\qquad r\sum_{i=1}^m\Big(\sum_T|s_i|_T\Big)^2>\sum_{x\in E(\mathcal T)\cap X(\mu)}\Big(\sum_T|x|_T\Big)^2 .$$

This corrects Theorem 6 and Corollary 3 of the source, which state $\delta(S,\mathcal T)>0$ (here $\mathrm{ssd}(S,\mathcal T)>0$) with no hypothesis $m\ge1$; when the mean is the star tree, $S$ and $X(S)$ are empty, both sides vanish, the printed inequality reads $0>0$, and the test says nothing. Its proof sums the strict inequalities for each $1\le i\le m$, which needs $m\ge1$. Accordingly, any **nonempty** candidate split set (orthant) for the mean with non-positive square-sum difference can be discarded before solving for the mean; the empty candidate set (the star tree) is never discarded by this test. The condition is not sufficient: several compatible split sets can satisfy it for the same sample.

## Depends on

- [Split-sum sufficient condition for a split in the BHV Fréchet mean](split-sum-sufficient-condition-for-a-split-in-the-bhv-frechet-mean.md)

## Expansion

For each tree $T$ let $(\mathcal A^T,\mathcal B^T)$ be the support of the geodesic from $\mu$ to $T$, and let $p(i,T)$ index the block containing $s_i$. At the mean, each split satisfies the first-order condition $\sum_T|s_i|_T>\sum_{T:\,s_i\in X(T)}\frac{\|B^T_{p(i,T)}\|}{\|A^T_{p(i,T)}\|}|s_i|_\mu$. Here $m\ge1$, so there is at least one strict summand. Squaring (the square of a sum of non-negative terms dominates the sum of squares) and summing over the $m\ge1$ strict inequalities, then regrouping by blocks with $\|A^T_j\|^2=\sum_{a\in A^T_j}|a|_\mu^2$, the right side collapses to $\sum_T\sum_{j\ge1}\|B^T_j\|^2$. The blocks $B^T_j$ with $j\ge1$ collect exactly the splits of $T$ incompatible with $\mu$, so this is the sum of squared weights over $E(\mathcal T)\cap X(\mu)$, an inequality in the data only. The corollary follows from Cauchy–Schwarz on sums of $r$ terms.

## Sources

- M. Anaya, O. Anipchenko-Ulaj, A. Ashfaq, J. Chiu, M. Kaiser, M. S. Ohsawa, M. Owen, E. Pavlechko, K. St. John, S. Suleria, K. Thompson, C. Yap, "Properties for the Fréchet mean in Billera-Holmes-Vogtmann treespace", arXiv:1907.05937 (2019), <https://doi.org/10.48550/arXiv.1907.05937>. Section 3.2 (Theorem 6, Corollary 2, Example 4, Definition 9, Corollary 3) and Section 4.
