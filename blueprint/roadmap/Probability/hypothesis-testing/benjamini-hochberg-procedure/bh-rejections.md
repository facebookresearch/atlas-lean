# Benjamini–Hochberg rejection set

Let $m \in \mathbb{N}$, $q \in \mathbb{R}$, $p_0, \dots, p_{m-1} \in \mathbb{R}$ and $k^*$ the [Benjamini–Hochberg step-up index](bh-index.md). The Benjamini–Hochberg procedure at level $q$ rejects the hypotheses whose p-value is at most $qk^*/m$:

$$R = \{i : p_i \le qk^*/m\}.$$
