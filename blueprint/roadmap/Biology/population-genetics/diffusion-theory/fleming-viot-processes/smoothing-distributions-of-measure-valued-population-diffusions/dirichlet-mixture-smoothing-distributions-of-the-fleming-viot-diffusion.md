# Dirichlet-mixture smoothing distributions of the Fleming–Viot diffusion

Let $\mathbb{Y}$ be a Polish type space, $\alpha$ a finite non-null Borel measure on $\mathbb{Y}$ with $\theta = \alpha(\mathbb{Y})$, and $\Pi_\alpha$ the law of a Dirichlet random measure with parameter $\alpha$. Let $X$ be the stationary Fleming–Viot diffusion with parent-independent mutation, whose transition function is

$$P_t(x, dx') = \sum_{m\ge0} d_m(t) \int_{\mathbb{Y}^m} \Pi_{\alpha + \sum_{i\le m}\delta_{y_i}}(dx')\, x^{m}(dy_1,\dots,dy_m),$$

where $d_m(t)$ is the law at time $t$ of the death process from $\infty$ with rates $n(\theta+n-1)/2$. At times $0 = t_0 < t_1 < \dots < t_N$ one observes samples $Y^1_{t_j}, Y^2_{t_j}, \dots \mid X_{t_j} = x$ that are i.i.d. from $x$.

1. **Finite mixture smoothing law.** If the whole dataset $\mathbf{Y}_{t_{0:N}}$ has $K$ distinct values $y_1,\dots,y_K$, then for each $0 \le i \le N$ there are a finite set $\mathcal{M} \subset \mathbb{Z}_+^K$ and weights $w_{\mathbf{m}} \ge 0$ summing to one with

$$\mathcal{L}(X_{t_i} \mid \mathbf{Y}_{t_{0:N}}) = \sum_{\mathbf{m}\in\mathcal{M}} w_{\mathbf{m}}\, \Pi_{\alpha + \sum_{j=1}^K m_j \delta_{y_j}} .$$

2. **One-step form.** Given data at $t_{i-1}, t_i, t_{i+1}$ with multiplicity vectors $\mathbf{n}_{i-1}, \mathbf{n}_i, \mathbf{n}_{i+1}$, and $\Delta_i = t_i - t_{i-1}$, $\Delta_{i+1} = t_{i+1} - t_i$,

$$\mathcal{L}(X_{t_i} \mid \mathbf{Y}_{i-1}, \mathbf{Y}_i, \mathbf{Y}_{i+1}) = \sum_{\mathbf{0}\le\mathbf{k}_{i-1}\le\mathbf{n}_{i-1}} \sum_{\mathbf{0}\le\mathbf{k}_{i+1}\le\mathbf{n}_{i+1}} w_{\mathbf{k}_{i-1},\mathbf{n}_i,\mathbf{k}_{i+1}}(\Delta_i,\Delta_{i+1})\, \Pi_{\alpha + \sum_j (k_{i-1,j}+n_{i,j}+k_{i+1,j})\delta_{y_j}} .$$

3. **Weights for discrete $P_0 = \alpha/\theta$.** With $p_{\mathbf{n},\mathbf{k}}(t)$ the transition probabilities of the typed Kingman death process (rates $m_j(\theta+|\mathbf{m}|-1)/2$ from $\mathbf{m}$ to $\mathbf{m}-\mathbf{e}_j$) and $m(\cdot)$ the Dirichlet–categorical marginal,

$$w_{\mathbf{k}_{i-1},\mathbf{n}_i,\mathbf{k}_{i+1}} \propto p_{\mathbf{n}_{i-1},\mathbf{k}_{i-1}}(\Delta_i)\, p_{\mathbf{n}_{i+1},\mathbf{k}_{i+1}}(\Delta_{i+1})\, \frac{m(\mathbf{k}_{i-1}+\mathbf{n}_i+\mathbf{k}_{i+1})}{m(\mathbf{k}_{i-1})\, m(\mathbf{n}_i)\, m(\mathbf{k}_{i+1})} .$$

For nonatomic $P_0$ the weights take explicit rising-factorial forms in which components carrying types observed at more than one time receive weights of larger order.

## Depends on

- [Ethier–Griffiths transition function of the Fleming–Viot process](../ethier-griffiths-transition-function.md)
- [Dirichlet-process stationary law of the Fleming–Viot process](../dirichlet-process-stationary-law.md)

## Expansion

Project onto finite partitions, where the signal is a $K$-type Wright–Fisher diffusion with moment dual given by Kingman's typed coalescent. The likelihood of past and future data given the current state is then a finite mixture of the functions $h(\mathbf{x}, \mathbf{k}) \propto \mathbf{x}^{\mathbf{k}}$ over the surviving lineage counts $\mathbf{k}$; by reversibility the backward propagation equals the forward one. Multiplying these mixtures by the present likelihood and the Dirichlet prior gives a Dirichlet mixture; a martingale argument over refining partitions lifts it to the measure-valued signal. The general $N$-point law follows by recursion.

## Sources

- Filippo Ascolani, Antonio Lijoi and Matteo Ruggiero, "Smoothing distributions for conditional Fleming–Viot and Dawson–Watanabe diffusions", Bernoulli 29 (2023), 1410–1434, <https://doi.org/10.3150/22-BEJ1504>. Numbering follows the arXiv version, arXiv:2204.12738 (2022): Theorem 1.1, Theorem 3.4, Proposition 3.6 and Theorem 4.4, <https://doi.org/10.48550/arXiv.2204.12738>.
