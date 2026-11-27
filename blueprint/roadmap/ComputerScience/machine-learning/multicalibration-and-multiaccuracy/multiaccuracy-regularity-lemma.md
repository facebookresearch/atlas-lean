# Multiaccuracy is the Trevisan–Tulsiani–Vadhan regularity lemma

Let $F$ be a class of functions $X \to [-1,1]$, $\mu$ a distribution on $X$, and $g : X \to [0,1]$ arbitrary. For every $\alpha > 0$ there is a function $h : X \to [0,1]$ computed by a circuit of size $\mathrm{poly}(\log|X|, 1/\alpha)$ with $O(1/\alpha^2)$ oracle gates for members of $F$ such that

$$
\big| \mathbb{E}_{x \sim \mu}[f(x)(g(x) - h(x))] \big| \le \alpha \quad \text{for all } f \in F .
$$

Viewing $g = p^*$ as the Bayes predictor and $F = \mathcal{C}$, such an $h$ is exactly an $\alpha$-multiaccurate predictor of low complexity relative to $\mathcal{C}$. Analogously, multicalibrated predictors give a strengthened regularity lemma in which the approximation holds on every level set of $h$; from it one derives Impagliazzo's hard-core lemma with optimal density and the dense model theorem.

## Proof sketch

The regularity lemma is proved by the same energy increment as multiaccuracy: start with $h = 1/2$; while some $f \in F$ has $|\mathbb{E}[f(g - h)]| > \alpha$, add $\pm\alpha f$ with the sign of that correlation and truncate to $[0,1]$, which lowers $\mathbb{E}(g - h)^2$ by $\alpha^2$. For the hard-core lemma, a multicalibrated partition for the function relative to $F$ splits the domain into pieces on which the function looks like a coin of bias $v_P$; each piece carries a hard-core distribution of density $2\min(v_P, 1-v_P)$, and gluing them gives the optimal density.

## Depends on

- [Multicalibrated predictors](multicalibrated-predictor.md)
- [Multiaccurate predictors](multiaccurate-predictor.md)

## Proof depends on

- [Each multiaccuracy correction decreases the squared distance to the Bayes predictor](multiaccuracy-correction-potential-decrease.md)

## Sources

- S. Casacuberta, C. Dwork, S. Vadhan, "Complexity-Theoretic Implications of Multicalibration", STOC (2024), arXiv:2312.17223, Theorem 1.1 and Section 1.4.
- L. Trevisan, M. Tulsiani, S. Vadhan, "Regularity, Boosting, and Efficiently Simulating Every High-Entropy Distribution", CCC (2009).
