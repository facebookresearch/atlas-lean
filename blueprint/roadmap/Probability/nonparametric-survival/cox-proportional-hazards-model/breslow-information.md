# Breslow information

For observed times $T_i$, event indicators $\delta_i \in \{0, 1\}$ and group labels $g_i \in \{0, 1\}$, the Breslow (Cox) information is

$$\sum_{i : \delta_i = 1} \frac{n_1(T_i)\, n_0(T_i)}{n(T_i)^2}, \qquad n_0(T_i) = n(T_i) - n_1(T_i),$$

summed over the events, with $n(T_i)$ the [number at risk](num-at-risk.md) and $n_1(T_i)$ the [number of group-1 subjects at risk](num-at-risk-in.md). It is $-\ell''(0)$ for a group indicator, not the tied log-rank variance: for one tied risk set with $n = 4$, $n_1 = 2$ and $d = 2$ events it gives $1/2$, while the hypergeometric log-rank variance is $1/3$. It equals the log-rank variance only when the event times are distinct (so each risk set contributes at most one event).
