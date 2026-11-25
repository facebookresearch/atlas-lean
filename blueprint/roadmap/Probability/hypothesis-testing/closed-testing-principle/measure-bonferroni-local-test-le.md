# Level of the Bonferroni local test

Let $\mu$ be a measure on $\Omega$, $p_0, \dots, p_{m-1} : \Omega \to \mathbb{R}$ and $H_0 \subseteq \{0, \dots, m-1\}$ such that each $p_i$, $i \in H_0$, is a valid p-value under $\mu$. For every $\alpha \in [0, 1]$, the [Bonferroni local test](bonferroni-local-test.md) of $H_{H_0}$ has level $\alpha$:

$$\mu(\exists j \in H_0 : p_j \le \alpha/|H_0|) \le \alpha.$$
