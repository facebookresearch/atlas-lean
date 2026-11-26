# Global functions on the p-biased cube

Let $\mu_p$ be the $p$-biased product measure on $\{0,1\}^n$ and $f : \{0,1\}^n \to \mathbb{R}$. For $S \subseteq [n]$ and $x \in \{0,1\}^S$ let $f_{S \to x}$ denote the restriction of $f$ obtained by fixing the coordinates in $S$ to $x$. The function $f$ is **$(r, \varepsilon)$-global** if

$$
\bigl\| f_{S \to x} \bigr\|_{L^2(\mu_p)} \le \varepsilon \quad \text{for every } S \text{ with } |S| \le r \text{ and every } x \in \{0,1\}^S.
$$

For a Boolean $f$ (the indicator of a set $\mathcal{A}$) this says that no restriction of at most $r$ coordinates increases the measure of $\mathcal{A}$ beyond $\varepsilon^2$. Let $D_S$ be the composition, over $i \in S$, of the normalized discrete derivatives $D_i f = \sqrt{p(1-p)}\,(f_{i \to 1} - f_{i \to 0})$, so that $D_S f = (p(1-p))^{|S|/2} \sum_{x \in \{0,1\}^S} (-1)^{|S| - |x|} f_{S \to x}$, where $|x|$ is the number of ones in $x$. The **generalized $S$-influence** is

$$
I_S(f) = \frac{\mathbb{E}\bigl[(D_S f)^2\bigr]}{(p(1-p))^{|S|}} = \Bigl\| \sum_{x \in \{0,1\}^S} (-1)^{|S| - |x|} f_{S \to x} \Bigr\|_{L^2(\mu_p)}^2 ,
$$

the squared norm of the unnormalized alternating difference. For $f(x) = x_i$ and $S = \{i\}$ this gives $I_S(f) = 1$, the ordinary influence $\|f_{i \to 1} - f_{i \to 0}\|_2^2$.

## Depends on

- [Influence of a coordinate](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/influences-and-the-noise-operator-on-the-boolean/bool-influence.md)

## Sources

- P. Keevash, N. Lifshitz, E. Long, D. Minzer, "Hypercontractivity for global functions and sharp thresholds", Journal of the American Mathematical Society 37 (2024), arXiv:1906.05568.
- P. Keevash, N. Lifshitz, E. Long, D. Minzer, "Global hypercontractivity and its applications", arXiv:2103.04604 (2021).
