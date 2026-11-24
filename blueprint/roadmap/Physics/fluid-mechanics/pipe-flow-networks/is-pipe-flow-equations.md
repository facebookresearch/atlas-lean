# Pipe-flow equations of a network: node balance and quadratic head loss

Let $V$ and $E$ be finite sets of nodes and arcs, each arc $e$ running from its tail $t(e)$ to its
head $h(e)$, and let $r$ (resistances) and $q$ (arc flows) be real functions on $E$ and $d$ (nodal
net inflows) and $H$ (heads) real functions on $V$. The pipe-flow equations hold when

- $\sum_{h(e) = i} q_e - \sum_{t(e) = i} q_e = d_i$ for every node $i$ (net inflow from the arcs);
- $H_{t(e)} - H_{h(e)} = r_e q_e |q_e|$ for every arc $e$ (quadratic head loss).

In matrix form these are $B q = d$ and $-B^\top H = (r_e q_e |q_e|)_e$ with the signed incidence
matrix $B_{ie} = [h(e) = i] - [t(e) = i]$; parallel and antiparallel arcs stay distinct, and a loop
arc has a zero column. Here $H$ is the piezometric head, $q_e$ the volumetric flow from $t(e)$ to
$h(e)$ and $d_i$ is positive at consumers and negative at sources. The resistances are
unconstrained, so a negative resistance (an active element) can satisfy the equations;
[passive pipe flows](is-passive-pipe-flow.md) add $r_e \geq 0$. No existence of solutions is
claimed.
