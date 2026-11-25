# Coordinate ascent along an update schedule

Let $X$, $y$, $\sigma_e^2$, $\pi$ be as for the [coordinate-ascent update](cavi-update.md), let $q = (q_1, \dots, q_m)$ be measures on $\mathbb{R}$, and let $s : \mathbb{N} \to \{1, \dots, m\}$ be an update schedule. Coordinate ascent along $s$ is the sequence of factor families defined by $q^{(0)} = q$ and, for each $t \ge 0$, $q^{(t+1)}$ is the [coordinate-ascent step](cavi-step.md) of $q^{(t)}$ at $s(t)$: at time $t$ the factor $s(t)$ is updated.
