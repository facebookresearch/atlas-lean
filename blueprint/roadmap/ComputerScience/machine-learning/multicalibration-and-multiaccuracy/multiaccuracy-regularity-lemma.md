# Multiaccuracy is the Trevisan–Tulsiani–Vadhan regularity lemma

Let $X$ be a finite domain whose elements are encoded as bit strings of length $\lceil \log_2 |X| \rceil$ (the circuit inputs), $F$ a class of functions $X \to [-1,1]$, $\mu$ a distribution on $X$, and $g : X \to [0,1]$ arbitrary. For every $\alpha > 0$ there is a function $h : X \to [0,1]$ computed by a circuit on these encoded inputs of size $\mathrm{poly}(\log|X|, 1/\alpha)$ with $O(1/\alpha^2)$ oracle gates for members of $F$ such that

$$
\big| \mathbb{E}_{x \sim \mu}[f(x)(g(x) - h(x))] \big| \le \alpha \quad \text{for all } f \in F .
$$

Viewing $g = p^*$ as the Bayes predictor and $F = \mathcal{C}$, such an $h$ is exactly an $\alpha$-multiaccurate predictor of low complexity relative to $\mathcal{C}$. Analogously, multicalibrated predictors give a strengthened regularity lemma (the Multicalibration Theorem of Hébert-Johnson et al. in the form of Casacuberta, Dwork and Vadhan, Theorem 1.2), stated there for a class $F$ of functions $X \to [0,1]$ and with a second parameter $\gamma > 0$: there is a partition $\mathcal{P}$ of $X$ into $O(1/\alpha)$ parts, computed by a circuit of size $\mathrm{poly}(1/\alpha, 1/\gamma, \log|X|)$ with $O(1/\alpha^2)$ oracle gates for members of $F$, such that $\big|\mathbb{E}_{x \sim \mu|_P}[f(x)(g(x) - v_P)]\big| \le \alpha$ with $v_P = \mathbb{E}_{x \sim \mu|_P}[g(x)]$ for every $f \in F$ and every part $P$ with $\mu(P) \ge \gamma$. Parts of mass below $\gamma$ carry no guarantee; together they have mass at most $O(\gamma/\alpha)$, which is small when $\gamma \ll \alpha$. On each part of mass at least $\gamma$, $g$ is thus indistinguishable from the constant $v_P$, and from this one derives Impagliazzo's hard-core lemma with optimal density and the dense model theorem (Theorems 1.4 and 1.8 of the source).

## Proof sketch

The regularity lemma is proved by the same energy increment as multiaccuracy: start with $h = 1/2$; while some $f \in F$ has $|\mathbb{E}[f(g - h)]| > \alpha$, add $\pm\alpha f$ with the sign of that correlation and truncate to $[0,1]$, which lowers $\mathbb{E}(g - h)^2$ by $\alpha^2$. For the hard-core lemma, a multicalibrated partition for the function relative to $F$ splits the domain into pieces; on each piece of mass at least $\gamma$ the function looks like a coin of bias $v_P$ and carries a hard-core distribution of density $2\min(v_P, 1-v_P)$, and gluing these, at a loss controlled by the $O(\gamma/\alpha)$ mass of the small pieces, gives the optimal density.

## Depends on

- [Multicalibrated predictors](multicalibrated-predictor.md)
- [Multiaccurate predictors](multiaccurate-predictor.md)

## Proof depends on

- [Each multiaccuracy correction decreases the squared distance to the Bayes predictor](multiaccuracy-correction-potential-decrease.md)

## Sources

- S. Casacuberta, C. Dwork, S. Vadhan, "Complexity-Theoretic Implications of Multicalibration", STOC (2024), arXiv:2312.17223, Theorems 1.1, 1.2, 1.4 and 1.8, Section 1.4.
- L. Trevisan, M. Tulsiani, S. Vadhan, "Regularity, Boosting, and Efficiently Simulating Every High-Entropy Distribution", CCC (2009).
