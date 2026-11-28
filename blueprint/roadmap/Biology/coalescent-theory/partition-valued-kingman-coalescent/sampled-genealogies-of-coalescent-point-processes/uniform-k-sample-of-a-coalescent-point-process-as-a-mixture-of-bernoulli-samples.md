# Uniform k-sample of a coalescent point process as a mixture of Bernoulli samples

Let a CPP of height $T$ have inverse tail distribution $F$ (node depths i.i.d. with $\mathbb{P}(H > t) = 1/F(t)$, stopped at the first value exceeding $T$) and $a = \mathbb{P}(H < T)$. Fix $k \ge 1$. Let $\Pi_k$ be the law of the oriented tree spanned by $k$ tips chosen uniformly from the CPP conditioned to have at least $k$ tips, and, for $y \in (0,1)$, let $\Gamma_{y,k}$ be the law of the tree spanned by a Bernoulli sample (each tip kept independently with probability $y$) conditioned to have exactly $k$ sampled tips. A Bernoulli-sampled CPP is again a CPP, with inverse tail distribution $F_y = 1 - y + yF$.

**Theorem.**

$$\Pi_k = \int_0^1 \mu_k(dy)\,\Gamma_{y,k}, \qquad \mu_k(dy) = \frac{k(1-a)\,y^{k-1}}{\big(1 - a(1-y)\big)^{k+1}}\,dy .$$

**Corollary (sampling recipe).** A tree with law $\Pi_k$ is obtained by drawing $Y \sim \mu_k$ and then, given $Y = y$, drawing $k - 1$ i.i.d. node depths with density $c^{-1}f_y$ on $(0,T)$, where $f_y = F_y'/F_y^2$ and

$$c = 1 - \frac{1}{F_y(T)} = \frac{ay}{1 - a(1-y)} .$$

**Corollary (likelihood).** The likelihood of a tree $\tau$ with law $\Pi_k$ and node depths $x_1 < \dots < x_{k-1}$ is

$$\mathcal{L}(\tau \mid k) = C(\tau)\,\frac{k(1-a)}{a^{k-1}}\int_0^1 \frac{dy}{\big(1 - a(1-y)\big)^2}\prod_{i=1}^{k-1} f_y(x_i),$$

with $C(\tau) = 1$ for oriented trees and $C(\tau) = 2^{k-1-\alpha(\tau)}$ for non-oriented trees with $\alpha(\tau)$ cherries.

## Depends on

- [Reduced splitting trees are coalescent point processes](reduced-splitting-trees-are-coalescent-point-processes.md)

## Expansion

The total number of tips $N$ is shifted geometric with failure probability $a$. Choosing a uniform $k$-subset of $\{1,\dots,N\}$ given $N \ge k$ has the same joint law as the following two-stage experiment: draw $Y$ with density $\mu_k$, then run i.i.d. Bernoulli($y$) marks along a geometric sequence of tips and stop at the $k$-th marked tip (a Beta–negative-binomial identity, checked by comparing the probabilities of every pattern of selected positions). Because the node depths of a CPP are i.i.d. and independent of which tips are selected, the subtree on Bernoulli-selected tips is again a CPP, with the depth between consecutive selected tips being the maximum of a geometric number of depths, which yields $F_y = 1 - y + yF$. Conditioning on $k$ selected tips makes the $k - 1$ depths i.i.d. with density $f_y$ restricted to $(0,T)$.

## Sources

- Amaury Lambert, *The coalescent of a sample from a binary branching process*, Theor. Popul. Biol. 122 (2018), 30–35. <https://doi.org/10.1016/j.tpb.2018.04.005> Proposition 2, Theorem 3, Corollary 4, Corollary 5, Lemma 6. Locators use the numbering of the preprint, titled *The genealogy of a sample from a binary branching process*, arXiv:1710.02220.
