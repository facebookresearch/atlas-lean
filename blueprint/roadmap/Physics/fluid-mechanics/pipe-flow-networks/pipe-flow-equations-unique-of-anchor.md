# Uniqueness of pipe-network flows and heads with one anchored head

Let $V$ and $E$ be finite sets of nodes and arcs, each arc $e$ running from its tail $t(e)$ to its
head $h(e)$, and suppose that the undirected graph on $V$ in which $u \neq v$ are adjacent when some
arc joins them in either direction is connected. Let the resistances satisfy $r_e > 0$ for every
arc. If $(q_1, H_1)$ and $(q_2, H_2)$ both solve the pipe-flow equations with the same nodal net
inflows $d$, that is $\sum_{h(e) = i} q_e - \sum_{t(e) = i} q_e = d_i$ for every node $i$ and
$H_{t(e)} - H_{h(e)} = r_e q_e |q_e|$ for every arc $e$, and $H_1(v_0) = H_2(v_0)$ at some node
$v_0$, then $q_1 = q_2$ and $H_1 = H_2$.
