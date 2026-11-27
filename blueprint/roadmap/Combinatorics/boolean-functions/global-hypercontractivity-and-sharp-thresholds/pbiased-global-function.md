# Global functions on the p-biased cube

Let $\mu_p$ be the $p$-biased product measure on $\{0,1\}^n$ and $f : \{0,1\}^n \to \mathbb{R}$. For $S \subseteq [n]$ and $x \in \{0,1\}^S$ let $f_{S \to x}$ denote the restriction of $f$ obtained by fixing the coordinates in $S$ to $x$, and write $f_{J \to 1}$ when every coordinate of $J$ is fixed to $1$. Two notions of globalness appear in the literature.

**Measure globalness (Keevash–Lifshitz–Long–Minzer).** A Boolean $f : \{0,1\}^n \to \{0,1\}$ is **$(r, \delta)$-measure-global** if

$$
\mu_p\bigl(f_{J \to 1}\bigr) \le \mu_p(f) + \delta \quad \text{for every } J \subseteq [n] \text{ with } |J| \le r.
$$

This is the notion that Keevash, Lifshitz, Long and Minzer call $(r, \delta)$-global (Definition 4.1).

**Restriction-norm globalness.** The function $f$ is **$(r, \varepsilon)$-global** if

$$
\bigl\| f_{S \to x} \bigr\|_{L^2(\mu_p)} \le \varepsilon \quad \text{for every } S \text{ with } |S| \le r \text{ and every } x \in \{0,1\}^S.
$$

This is the $p$-biased form of the $L^2$-restriction notion that Filmus, Kindler, Lifshitz and Minzer use on the symmetric group (Definition 1.3); Keller, Lifshitz and Marcus state their sharp hypercontractive inequality on general finite product spaces under the related condition $\|f_{S \to x}\|_2 \le r^{|S|} \|f\|_2$ (Theorem 1.3). For a Boolean $f$ (the indicator of a set $\mathcal{A}$) one has $\|f_{S \to x}\|_2^2 = \mu_p(f_{S \to x})$, so $(r, \varepsilon)$-globalness says that every restriction of at most $r$ coordinates gives $\mathcal{A}$ measure at most $\varepsilon^2$.

Let $D_S$ be the composition, over $i \in S$, of the normalized discrete derivatives $D_i f = \sqrt{p(1-p)}\,(f_{i \to 1} - f_{i \to 0})$, so that $D_S f = (p(1-p))^{|S|/2} \sum_{x \in \{0,1\}^S} (-1)^{|S| - |x|} f_{S \to x}$, where $|x|$ is the number of ones in $x$. The **generalized $S$-influence** (Keevash–Lifshitz–Long–Minzer, Definition 1.2) is

$$
I_S(f) = \frac{\mathbb{E}\bigl[(D_S f)^2\bigr]}{(p(1-p))^{|S|}} = \Bigl\| \sum_{x \in \{0,1\}^S} (-1)^{|S| - |x|} f_{S \to x} \Bigr\|_{L^2(\mu_p)}^2 ,
$$

the squared norm of the unnormalized alternating difference. For $f(x) = x_i$ and $S = \{i\}$ this gives $I_S(f) = 1$, the ordinary influence $\|f_{i \to 1} - f_{i \to 0}\|_2^2$.

## Depends on

- [Influence of a coordinate](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/influences-and-the-noise-operator-on-the-boolean/bool-influence.md)

## Sources

- P. Keevash, N. Lifshitz, E. Long, D. Minzer, "Hypercontractivity for global functions and sharp thresholds", Journal of the American Mathematical Society 37 (2024) 245-279, arXiv:1906.05568, Definitions 1.2 and 4.1.
- Y. Filmus, G. Kindler, N. Lifshitz, D. Minzer, "Hypercontractivity on the symmetric group", Forum of Mathematics, Sigma 12 (2024) e6, arXiv:2009.05503, Definition 1.3.
- N. Keller, N. Lifshitz, O. Marcus, "Sharp hypercontractivity for global functions", Journal of the European Mathematical Society (2026), arXiv:2307.01356, Theorem 1.3.
