# Log-rank numerator: observed minus expected events

For observed times $T_i$, event indicators $\delta_i \in \{0, 1\}$ and group labels $g_i \in \{0, 1\}$ with [group indicator](group-indicator.md) $z_i$, the log-rank numerator is the observed minus expected number of group-1 events,

$$O - E = \sum_{i : \delta_i = 1} \Big(z_i - \frac{n_1(T_i)}{n(T_i)}\Big),$$

with $n(T_i)$ the [number at risk](num-at-risk.md) and $n_1(T_i)$ the [number of group-1 subjects at risk](num-at-risk-in.md).
