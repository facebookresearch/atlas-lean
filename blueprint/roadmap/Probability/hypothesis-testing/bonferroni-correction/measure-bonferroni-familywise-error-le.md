# The Bonferroni procedure controls the FWER

Let $\mu$ be a measure on $\Omega$, $p_0, \dots, p_{m-1} : \Omega \to \mathbb{R}$ and $H_0 \subseteq \{0, \dots, m-1\}$ the set of true null hypotheses, each $p_i$ with $i \in H_0$ being a valid p-value under $\mu$. For every $\alpha \in [0,1]$, the probability that the [Bonferroni procedure](bonferroni-rejections.md) at level $\alpha$ rejects at least one true null is at most $\alpha$:

$$\mu(\exists i \in H_0 : p_i \le \alpha/m) \le \alpha.$$
