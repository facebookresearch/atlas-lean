# Identification of the hazard under interval censoring

Under interval censoring on a finite grid, an inspection set $S$ with law $p_S$ is independent of the event time $T \sim p_T$, and one observes $S$ together with the inspection times in $S$ at or after $T$. Write $h(j) = P(T = j) / P(T \ge j)$ for the [discrete hazard](../../censored-survival-data/hazard.md), with $0/0 = 0$, the value when $P(T \ge j) = 0$. If two event-time laws give the same observed-data law, $P(j \in S) > 0$ or $j$ is the last grid point, and $P(j - 1 \in S) > 0$ or $j = 0$, then they have the same hazard at $j$.
