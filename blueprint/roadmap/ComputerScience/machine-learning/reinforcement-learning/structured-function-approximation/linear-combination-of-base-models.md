# Linear combination of base models

Given $K$ base MDPs and a feature map into the simplex $\Delta_{d-1}$, the linearly combined model with parameter $W$ mixes the base transition and reward laws with state-action dependent weights $W\phi(s,a) \in \Delta_{K-1}$. The true environment is assumed to be such a mixture, exactly or up to an $\ell_1$ error $\theta$.

**Setting.** Episodic MDPs $(\mathcal{S}, \mathcal{A}, P, R, H, P_1)$ with transition kernel $P : \mathcal{S}\times\mathcal{A} \to \Delta(\mathcal{S})$, reward law $R : \mathcal{S}\times\mathcal{A} \to \Delta([0,1])$, horizon $H$, initial distribution $P_1$, and total reward $\sum_{h=1}^H r_h \in [0,1]$ almost surely under every policy. The learner is given base models $M_1, \dots, M_K$ sharing $\mathcal{S}, \mathcal{A}, H, P_1$ and differing in $(P^k, R^k)$, and a feature map $\phi : \mathcal{S} \times \mathcal{A} \to \Delta_{d-1}$, the probability simplex in $\mathbb{R}^d$.

**Definition.** For

$$
W \in \mathcal{W}_0 = \Big\{ W \in [0,1]^{K \times d} : \sum_{i=1}^{K} W_{ij} = 1 \text{ for all } j \in [d] \Big\},
$$

the model $M(W)$ has

$$
P^W(\cdot \mid s,a) = \sum_{k=1}^{K} [W\phi(s,a)]_k\, P^k(\cdot \mid s,a), \qquad R^W(\cdot \mid s,a) = \sum_{k=1}^{K} [W\phi(s,a)]_k\, R^k(\cdot \mid s,a).
$$

Since the columns of $W$ and the vector $\phi(s,a)$ are probability vectors, $W\phi(s,a) \in \Delta_{K-1}$ and $M(W)$ is again an MDP. The *approximation error* of the class for the true environment $M^\ast = (P^\ast, R^\ast)$ is

$$
\theta = \min_{W \in \mathcal{W}} \sup_{(s,a)} \Big( \lVert P^\ast(\cdot\mid s,a) - P^W(\cdot\mid s,a) \rVert_1 + \lVert R^\ast(\cdot\mid s,a) - R^W(\cdot\mid s,a) \rVert_1 \Big),
$$

attained at $W^\ast$; $\theta = 0$ is the realizable case $M^\ast = M(W^\ast)$.

**Special cases.** With $d = 1$ and $\phi \equiv 1$ the class is the set of global convex combinations of the base models. With $\phi$ the indicator vector of a partition $\{\mathcal{X}_i\}$ of $\mathcal{S}\times\mathcal{A}$, the mixing weights are constant on each cell.

## Depends on

None.

## Proof depends on

None.

## Expansion

For a function $f$ on next states, $\mathbb{E}_{M(W)}[r + f(s') \mid s,a] = [W\phi(s,a)]^{\mathsf T}\bar V(s,a)$, where $\bar V(s,a)_k = \mathbb{E}_{M_k}[r + f(s') \mid s,a]$. This bilinear form in $W$ and $\phi$ is what makes the class learnable with sample complexity independent of $|\mathcal{S}|$ and $|\mathcal{A}|$. Like the [linear mixture MDP](linear-mixture-mdp.md), it is a model class with a finite-dimensional unknown; here the weights depend on $(s,a)$ through $\phi$ and must form a convex combination.

## Sources

- A. Modi, N. Jiang, A. Tewari and S. Singh, "Sample Complexity of Reinforcement Learning using Linearly Combined Model Ensembles", International Conference on Artificial Intelligence and Statistics (AISTATS 2020), PMLR 108:2010–2020. Numbers from arXiv:1910.10597v1: Section 2 (setting and notation), Definition 2.1, Examples 2.2–2.3, Eq. (1). <https://arxiv.org/abs/1910.10597v1>
