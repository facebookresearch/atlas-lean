# Coalescent point process of a linear-fractional Galton–Watson tree

**Setting.** Let $(Z_n)_{n \ge 0}$ be a Bienaymé-Galton-Watson process with $Z_0 = 1$ and $(p, r)$-*linear fractional* offspring law

$$\mathbb P(\xi = 0) = 1 - r, \qquad \mathbb P(\xi = k) = r p (1-p)^{k-1}, \quad k \ge 1,$$

with $0 < p < 1$, $0 \le r \le 1$, $p \ne r$, and mean $m = r/p$. Embed an infinitely old population in the plane in the usual monotone way and, for consecutive tips $i-1, i$ of the present generation, let $H_i$ be the number of generations back to their most recent common ancestor. The sequence $(H_i)_{i \ge 1}$ is the *coalescent point process* (CPP). For a fixed depth $T \in \mathbb N$, let $N_T = \min\{i \ge 1 : H_i > T\}$, set $H_0 = T$, and let $\mathbf T^{p,r}$ be the ultrametric oriented tree with node depths $H_1, \dots, H_{N_T - 1}$ (the genealogy of the tips descending from one ancestor $T$ generations back).

**Proposition (i.i.d. branch lengths).** The $H_i$ are i.i.d. with

$$\mathbb P(H_i > n) = \frac{r - p}{(1-p)\, m^n - (1 - r)}, \qquad n \ge 0.$$

Hence $N_T$ is geometric with failure probability $\mathbb P(H \le T)$, and for an ultrametric oriented tree $\tau$ with $n$ tips and node depths $x_1, \dots, x_{n-1} \in \{1, \dots, T\}$,

$$\mathbb P(\mathbf T^{p,r} = \tau) = \mathbb P(H > T) \prod_{i=1}^{n-1} \mathbb P(H = x_i), \qquad \mathbb P(\mathbf T^{p,r} = \tau \mid N_T = n) = \prod_{i=1}^{n-1} \frac{\mathbb P(H = x_i)}{\mathbb P(H \le T)}.$$

**Lemma (Bernoulli sampling).** Keep each tip independently with probability $y \in (0, 1)$ and let $H_{y,i}$ be the coalescence depth between consecutive kept tips. Then the $H_{y,i}$ are i.i.d. with

$$\mathbb P(H_{y,i} > n) = \frac{r - p}{y(1-p)\, m^n - [\,y(1-p) - (r-p)\,]}, \qquad n \ge 0.$$

The likelihood of a Bernoulli$(y)$-sampled tree is the formula above with $H$ replaced by $H_y$. The tail has the algebraic shape of a linear-fractional CPP tail with $p_y = 1 - y(1-p)$ and $r_y = 1 - y(1-p) + r - p$, but these need not be offspring-law parameters: for $p = y = 1/2$ and $r = 1$ they give $r_y = 5/4 > 1$.

**Embedding.** For $0 < r \le 1$, a $(p,r)$-linear-fractional process is the integer-time skeleton of a linear birth-death process started from one individual, with birth and death rates

$$\lambda = (1 - p)\,\frac{\log p - \log r}{p - r}, \qquad \mu = (1 - r)\,\frac{\log p - \log r}{p - r}.$$

## Depends on

- [Generation-size law of a Galton–Watson process](../../../../Probability/branching-processes/galton-watson-process/law.md)

## Expansion

Linear-fractional laws are mixtures of a point mass at $0$ and a shifted geometric law, and their generating functions are Möbius maps, closed under composition, so every generation size is again linear fractional; this makes the reduced tree renewal-like, so consecutive coalescence depths forget the past, which gives the i.i.d. property and the explicit tail. For Bernoulli sampling, the depth between consecutive kept tips is the maximum of a geometric$(y)$ number of independent copies of $H$, so $\mathbb P(H_y \le n) = y F(n) / (1 - (1-y)F(n))$ with $F(n) = \mathbb P(H \le n)$; solving for the tail gives the displayed formula, and independence of the blocks between consecutive kept tips gives the i.i.d. property. The tree likelihoods follow because the reduced tree is determined by its node depths, and conditioning on $N_T = n$ turns the geometric stopping into $n - 1$ i.i.d. draws of $H$ given $H \le T$.

## Sources

- Natalia Cardona-Tobón and Sandra Palau, "The coalescent of a sample from a linear-fractional branching process", *Theoretical Population Biology* 171 (2026), 22–28, <https://doi.org/10.1016/j.tpb.2026.05.001>. Numbering as in the preprint arXiv:2506.17470v1, <https://arxiv.org/abs/2506.17470v1>: Proposition 2.1, Lemma 2.2, Lemma 2.3, Lemma 2.4 and Lemma 3.1.
