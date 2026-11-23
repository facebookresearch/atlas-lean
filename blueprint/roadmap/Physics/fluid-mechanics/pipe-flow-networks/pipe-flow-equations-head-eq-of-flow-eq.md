# Heads of a pipe network are determined by the flows and one anchor

Let $V$ and $E$ be finite sets of nodes and arcs, each arc $e$ running from its tail $t(e)$ to its
head $h(e)$, and suppose that the undirected graph on $V$ in which $u \neq v$ are adjacent when some
arc joins them in either direction is connected. Call $(q, d, H)$, with arc flows $q$, nodal net
inflows $d$ and heads $H$, a solution of the pipe-flow equations for resistances $r$ when
$\sum_{h(e) = i} q_e - \sum_{t(e) = i} q_e = d_i$ for every node $i$ and
$H_{t(e)} - H_{h(e)} = r_e q_e |q_e|$ for every arc $e$. If $(q_1, d_1, H_1)$ and
$(q_2, d_2, H_2)$ are solutions for the same resistances with $q_1 = q_2$ and
$H_1(v_0) = H_2(v_0)$ at some node $v_0$, then $H_1 = H_2$. No sign condition on $r$ is needed.
