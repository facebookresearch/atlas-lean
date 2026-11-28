# Stopping rules sampled on a finite nonuniform schedule

Let $I$ be a linearly ordered time domain and $(\mathcal F_t)_{t\in I}$ a filtration. Fix a strictly increasing schedule $e_0 < \dots < e_m = T$ in $I$, where $m \ge 0$ and $T$ is the mandatory terminal date. For $k \in \mathbb{N}$, set $s_k = e_{\min(k,m)}$ and $\mathcal G_k = \mathcal F_{s_k}$, so the sampled filtration is constant after the terminal index.

The map $\iota \mapsto \tau = e_\iota$ is a bijection from stopping times for $(\mathcal G_k)$ taking values in $\{0,\dots,m\}$ to stopping times for $(\mathcal F_t)$ taking values in $\{e_0,\dots,e_m\}$. Its inverse recovers, at each sample point, the unique index of the stopping date. For any process $Z$, evaluating at the corresponding stopping dates gives $Z_\tau = Z_{e_\iota}$ pointwise. No probability measure or integrability assumption is needed. If $m=0$, the constant stopping index $0$ corresponds to the constant stopping date $T$.

## Sources

- The statement is derived on this page from its definitions and the linked results; no external source is followed.
