# Turning flows and link boundary flows

Let $E$ be a finite set of links, $C$ a set of commodities, and $q_c(e, e')$ the turning flow of commodity $c$ from link $e$ to link $e'$. On the network whose nodes are links and whose arcs are ordered pairs $(e, e')$, apply the incidence matrix (inflow minus outflow) to the aggregate turning flows $\sum_c q_c(e, e')$. At link $e$ the result is $\sum_c \sum_{e_0} q_c(e_0, e) - \sum_c \sum_{e'} q_c(e, e')$, the aggregate upstream boundary flow minus the aggregate downstream boundary flow.
