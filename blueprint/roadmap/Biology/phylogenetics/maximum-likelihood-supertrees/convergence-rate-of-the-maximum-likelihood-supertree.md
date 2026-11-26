# Convergence rate of the maximum likelihood supertree

Let $\mathcal{L}^*$ be a finite set of species with a resolved true species tree $T^*$ in the Billera–Holmes–Vogtmann (BHV) space $\mathcal{T}$ of metric phylogenetic trees on $\mathcal{L}^*$, with distance $d$. A tree-generating model $(\mathcal{P}_T)_{T \in \mathcal{T}}$ assigns, to each leaf subset $\mathcal{L} \subset \mathcal{L}^*$, a distribution $\mathcal{P}^{\mathcal{L}}_T$ on trees with leaf set $\mathcal{L}$. Gene trees $T_1, \dots, T_k$ with leaf sets $\mathcal{L}_1, \dots, \mathcal{L}_k$ are observed independently, $T_i \sim \mathcal{P}^{\mathcal{L}_i}_{T^*}$, and the **maximum likelihood (ML) supertree** is

$$
\hat T_k = \arg\max_{T \in \mathcal{T}} \ell_k(T), \qquad \ell_k(T) = \sum_{i=1}^k \log \mathcal{P}^{\mathcal{L}_i}_{T}(T_i).
$$

Assume:

1. **Weak covering property.** There are $c_1 > 0$, $\gamma > 1/2$ and $K > 0$ such that every 4-element subset $\mathcal{L} \subset \mathcal{L}^*$ satisfies $k^{-\gamma}\,|\{i \le k : \mathcal{L} \subset \mathcal{L}_i\}| \ge c_1$ for all $k \ge K$ (every quartet is sampled at least order $k^\gamma$ times).
2. **Identifiability.** For every $\mathcal{L}$, $d(T^*|_{\mathcal{L}}, T|_{\mathcal{L}}) > 0$ implies $\mathrm{KL}(\mathcal{P}^{\mathcal{L}}_{T^*}, \mathcal{P}^{\mathcal{L}}_{T}) > 0$.
3. **Regularity.** (a) All probabilities $\mathcal{P}^{\mathcal{L}}_T(T')$ are positive and $T \mapsto \log \mathcal{P}^{\mathcal{L}}_T(T')$ is locally Lipschitz with a constant independent of $T'$; (b) there are $c_2, c_3 > 0$ and $m \ge 2$ with $\mathrm{KL}(\mathcal{P}^{\mathcal{L}}_{T^*}, \mathcal{P}^{\mathcal{L}}_{T}) \ge c_3\, d(T^*|_{\mathcal{L}}, T|_{\mathcal{L}})^m$ whenever $d(T^*, T) \le c_2$.

**Theorem.** Under 1–3, for every $\delta > 0$ there are constants $C_\delta, K_\delta > 0$ such that for all $k \ge K_\delta$,

$$
d(\hat T_k, T^*) \le C_\delta \left( \frac{\log k}{k^{\gamma - 1/2}} \right)^{1/m}
$$

with probability at least $1 - \delta$. Under 1, 2 and 3(a) alone the ML supertree is consistent: $\hat T_k \to T^*$ in probability.

Condition 3(b) holds automatically when each $\mathcal{P}^{\mathcal{L}}_T(T')$ is analytic in $T$ near $T^*$, and it only needs to hold for the observed leaf sets $\mathcal{L}_i$.

## Expansion

Write the normalized empirical risk $R_k(T) = k^{-1}(\ell_k(T^*) - \ell_k(T))$. Its expectation is a sum of KL divergences over gene trees; since every quartet of $T^*$ appears in order $k^\gamma$ leaf sets, the expected risk is bounded below by $c\,k^{\gamma-1}\, d(T^*, T)^m$ near $T^*$ and by $c\,k^{\gamma-1}$ away from it. A uniform concentration bound shows $|R_k(T) - \mathbb{E} R_k(T)| \le c \log k / \sqrt{k}$ for all $T$ with high probability. Because $R_k(\hat T_k) \le 0$, the expected risk at $\hat T_k$ is at most $c \log k/\sqrt{k}$, which first forces $\hat T_k$ into a neighborhood of $T^*$ and then yields the stated rate. The covering exponent $\gamma > 1/2$ is exactly what makes the signal $k^{\gamma-1}$ dominate the noise $k^{-1/2}\log k$; the classical covering property of Steel and Rodrigo corresponds to $\gamma = 1$.

## Sources

- L. S. T. Ho and V. Dinh, *Convergence of maximum likelihood supertree reconstruction*, arXiv:2105.01723 (2021), Section 2 (Assumptions 2.1–2.3, Remarks 2.2–2.3), Theorem 1 and Corollary 1. <https://doi.org/10.48550/arXiv.2105.01723>
