# The unpolarized D-statistic numerator vanishes on a tree

Let $M$ be a [drift model](../patterson-s-f-statistics/drift-model.md) on a measure $\mu$ with lineage weights $w(X, e)$ and population frequencies $p_X$, and let $P_1, P_2, P_3, O$ be populations such that

$$\bigl(w(P_1, e) - w(P_2, e)\bigr)\bigl(w(P_3, e) - w(O, e)\bigr) = 0 \qquad \text{for every edge } e$$

(no edge lies on both the $P_1$–$P_2$ and the $P_3$–$O$ path, as on the tree $((P_1, P_2), P_3), O$). Suppose that $\omega \mapsto \mathbb{E}_{q(\omega)}[\mathrm{ABBA}]$ and $\omega \mapsto \mathbb{E}_{q(\omega)}[\mathrm{BABA}]$ are $\mu$-integrable, where $q = (p_{P_1}, p_{P_2}, p_{P_3}, p_O)$ and $\mathbb{E}_q$ is the [sampling expectation](sample-expect.md). Then

$$\int \mathbb{E}_{q}[\mathrm{ABBA}] \, d\mu = \int \mathbb{E}_{q}[\mathrm{BABA}] \, d\mu,$$

for the unpolarized [ABBA](abba.md) and [BABA](baba.md) indicators.
