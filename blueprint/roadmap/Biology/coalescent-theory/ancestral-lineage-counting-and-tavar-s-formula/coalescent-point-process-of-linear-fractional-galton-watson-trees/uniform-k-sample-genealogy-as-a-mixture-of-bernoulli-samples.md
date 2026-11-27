# Uniform k-sample genealogy as a mixture of Bernoulli samples

**Setting.** Let $(H_i)_{i \ge 1}$ be the coalescent point process of a supercritical Bienaymé-Galton-Watson process with $(p, r)$-linear fractional offspring law ($0 < p < 1$, $0 \le r \le 1$, $m = r/p > 1$), so the $H_i$ are i.i.d. with $\mathbb P(H > n) = (r-p)/((1-p)m^n - (1-r))$. Fix a depth $T \in \mathbb N$, let $N_T = \min\{i : H_i > T\}$ and $H_0 = T$, and let $\delta_T = \mathbb P(H > T)$. Conditionally on $N_T \ge k$, choose $k$ of the $N_T$ tips uniformly at random; the *$k$-sample tree* $\mathbf T_k$ has node depths $H_{k,0} = T, H_{k,1}, \dots, H_{k,k-1}$, where $H_{k,i}$ is the coalescence depth of the $(i-1)$-th and $i$-th sampled tips. For $y \in (0,1)$, the *Bernoulli$(y)$ sample tree* $\mathbf T_y$ keeps each tip independently with probability $y$; let $K$ be the number of kept tips and $H_{y,i}$ its node depths.

**Theorem.** Let

$$\mu_k(dy) = \frac{k\, \delta_T\, y^{k-1}}{\bigl(1 - (1-\delta_T)(1-y)\bigr)^{k+1}}\, dy, \qquad y \in (0,1),$$

a probability measure. For all $x_1, \dots, x_{k-1} \in \{1, \dots, T\}$ and $x_0 = T$,

$$\mathbb P\bigl(H_{k,0} = x_0, \dots, H_{k,k-1} = x_{k-1} \,\big|\, N_T \ge k\bigr) = \int_0^1 \mu_k(dy)\, \mathbb P\bigl(H_{y,0} = x_0, \dots, H_{y,k-1} = x_{k-1} \,\big|\, K = k\bigr).$$

**Corollary (sampling recipe and likelihood).** The law of $(H_{k,0}, \dots, H_{k,k-1})$ is obtained by drawing $Y \sim \mu_k$ and then, given $Y = y$, setting $H_{y,0} = T$ and drawing $H_{y,1}, \dots, H_{y,k-1}$ i.i.d. with

$$\mathbb P(H_{y,i} \le j \mid H_{y,i} \le T) = \frac{m^j - 1}{m^T - 1} \cdot \frac{r - p + y(1-p)(m^T - 1)}{r - p + y(1-p)(m^j - 1)}, \qquad 1 \le j \le T.$$

Consequently, for an ultrametric oriented tree $\tau$ with node depths $x_0 = T, x_1, \dots, x_{k-1}$, the likelihood of $(p, r)$ is

$$\mathcal L(p, r \mid \tau, k) = \int_0^1 \mu_k(dy) \prod_{i=1}^{k-1} \frac{\mathbb P(H_{y,i} = x_i)}{\mathbb P(H_{y,i} \le T)}.$$

## Depends on

- [Coalescent point process of a linear-fractional Galton–Watson tree](coalescent-point-process-of-a-linear-fractional-galton-watson-tree.md)

## Expansion

Give the sampling probability $Y$ the improper prior $y^{-1}dy$ on $(0,1)$ and define a measure $\mathbb Q$ on (independent CPP, Bernoulli$(Y)$ marks). A direct computation shows that, for every $m \ge k$ and every 0-1 pattern $\mathbf i$ with $k$ ones, $\mathbb P(N_T = m, \text{selected pattern} = \mathbf i \mid N_T \ge k)$ equals $\mathbb Q(\tilde N_T = m, \text{marks} = \mathbf i \mid K = k)$, and that $\mathbb Q(Y \in dy \mid K = k) = \mu_k(dy)$. Since in both schemes the sample node depths are maxima of the CPP depths over the blocks between consecutive selected tips, the two conditional laws of the sample trees coincide, and disintegrating over $Y$ gives the mixture. The conditional law given $Y = y$ is explicit because the node depths of a Bernoulli$(y)$ sample are i.i.d. with the explicit tail of the Bernoulli-sampling lemma. The same mixture identity was known for birth-death trees in continuous time; here it holds in discrete time with multiple mergers at a generation.

## Sources

- Natalia Cardona-Tobón and Sandra Palau, "The coalescent of a sample from a linear-fractional branching process", *Theoretical Population Biology* 171 (2026), 22–28, <https://doi.org/10.1016/j.tpb.2026.05.001>. Numbering as in the preprint arXiv:2506.17470v1, <https://arxiv.org/abs/2506.17470v1>: Lemma 2.7, Theorem 2.8 and Corollary 2.9.
