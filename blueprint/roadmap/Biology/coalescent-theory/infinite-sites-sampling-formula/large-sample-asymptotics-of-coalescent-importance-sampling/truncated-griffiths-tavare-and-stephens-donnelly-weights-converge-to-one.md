# Truncated Griffiths–Tavaré and Stephens–Donnelly importance weights converge to one

**Setting.** Let $p(\mathbf n)$ be the probability of an observed type configuration $\mathbf n \in \mathbb N^d$ under the Kingman coalescent with mutation (rate $\theta$, mutation matrix $P$), and let $p(\mathbf n - \mathbf v \mid \mathbf n)$ be the true backward transition probabilities of the block-counting chain. An importance sampler draws backward histories from a proposal $q$; truncated after $k$ steps from the sample $n\mathbf y_0^{(n)}$, its normalised weight is

$$W^{(n)}(k) = \frac{p(n\mathbf Y^{(n)}(k))}{p(n\mathbf y_0^{(n)})}\, C^{(n)}(k), \qquad c_q^{(n)}(\mathbf v \mid \mathbf y) = \frac{p(n\mathbf y \mid n\mathbf y - \mathbf v)}{q(n\mathbf y - \mathbf v \mid n\mathbf y)},$$

where $C^{(n)}$ multiplies the one-step costs $c_q^{(n)}$ along the path and $p(\cdot \mid \cdot)$ in the numerator of $c_q$ is the forward transition probability. Two classical proposals:

- **Griffiths–Tavaré (GT):** $q_{GT}(\mathbf n - \mathbf v \mid \mathbf n) \propto p(\mathbf n \mid \mathbf n - \mathbf v)$; its one-step cost is the same for every step type and satisfies

$$c_{GT}^{(n)}(\mathbf v \mid \mathbf y) = 1 - \frac1n\,\frac{d-1}{\|\mathbf y\|_1} + o(1/n).$$

- **Stephens–Donnelly (SD):** the true backward probabilities with the unknown conditional sampling probabilities replaced by $\hat\pi[j \mid \mathbf n] = \sum_i \frac{n_i}{\|\mathbf n\|+\theta}\sum_{m \ge 0}\big(\frac{\theta}{\|\mathbf n\|+\theta}\big)^m (P^m)_{ij}$; then

$$c_{SD}^{(n)}(\mathbf e_j \mid \mathbf y) = 1 + \frac1n\Big[\frac{1-\theta}{\|\mathbf y\|_1} - \frac{1}{y_j}\Big(1 - \sum_i \frac{y_i}{\|\mathbf y\|_1}\theta P_{ij}\Big)\Big] + o(1/n), \qquad c_{SD}^{(n)}(\mathbf e_i - \mathbf e_j \mid \mathbf y) = 1 + o(1).$$

**Theorem.** Assume $\mathbf y_0^{(n)} \to \mathbf y_0 \in \mathbb R^d_+$ with $\|\mathbf y_0\|_1 = 1$ and fix $t \in [0,1)$. Under the true backward distribution, as $n \to \infty$,

$$\frac{p(n\mathbf Y^{(n)}(\lfloor tn \rfloor))}{p(n\mathbf y_0^{(n)})} \Rightarrow (1-t)^{1-d}, \qquad C_{GT}^{(n)}(\lfloor tn \rfloor) \Rightarrow (1-t)^{d-1}, \qquad C_{SD}^{(n)}(\lfloor tn \rfloor) \Rightarrow (1-t)^{d-1},$$

hence $W_{GT}^{(n)}(\lfloor tn \rfloor) \Rightarrow 1$ and $W_{SD}^{(n)}(\lfloor tn \rfloor) \Rightarrow 1$. The same limit for the state, mutation counts and costs also holds when the chain is run under the GT or SD proposal instead of the true dynamics.

Thus both samplers, truncated at a fixed fraction $t$ of the sample size, are asymptotically exact in distribution: in the large-sample regime the proposal loses no information until few lineages remain.

## Depends on

- [Large-sample limit of cost functionals of the coalescent block-counting chain](large-sample-limit-of-coalescent-cost-functionals.md)

## Expansion

Plug the one-step expansions into the general cost limit. For GT, $a_j(\mathbf y) = -(d-1)/\|\mathbf y\|_1$ and $b_{ij} = 1$, so along $\mathbf y_0(1-u)$ the exponent is $-\int_0^t (d-1)/(1-u)\,du = (d-1)\ln(1-t)$, giving $(1-t)^{d-1}$. For SD the terms $1/y_j$ weighted by $y_{0,j}$ sum, together with the $\theta$ terms, to the same $(d-1)/(1-u)$ integrand, and the mutation costs tend to $1$. The ratio of sampling probabilities is the reciprocal: a configuration of size $m$ in $d$ types has probability of order $m^{1-d}$ times a function of frequencies, and the frequencies are frozen along the ray. The product is therefore $1$.

## Sources

- Martina Favero and Jere Koskela, "Large-sample analysis of cost functionals for inference under the coalescent", *Stochastic Processes and their Applications* 195 (2026), 104894, <https://doi.org/10.1016/j.spa.2026.104894>. Numbering as in the preprint arXiv:2412.06004v2, <https://arxiv.org/abs/2412.06004v2>: Propositions 4.1, 4.2, 5.2 and Theorem 5.3.
