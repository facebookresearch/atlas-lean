# Sub-additivity (tensorization) of entropy

Let $n$ be a natural number, $0 < p < 1$, and $g : \{0, 1\}^n \to [0, \infty)$. Under the $p$-biased product measure $\mu_p$ on $\{0, 1\}^n$,

$$\mathrm{Ent}(g) \le \sum_{e=1}^{n} \mathbb{E}\big[\mathrm{Ent}_e(g)\big],$$

where $\mathrm{Ent}(g) = \mathbb{E}[g \log g] - \mathbb{E}[g] \log \mathbb{E}[g]$ is the [entropy](esd-ent.md) and $\mathrm{Ent}_e(g)$ the [conditional entropy in coordinate $e$](esd-ent-coord.md), with $0 \log 0 = 0$.
