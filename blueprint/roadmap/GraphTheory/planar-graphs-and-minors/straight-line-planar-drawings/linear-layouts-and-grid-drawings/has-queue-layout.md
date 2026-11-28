# Queue layout

A simple graph $G$ has a $k$-queue layout when there are an injective map $\mathrm{ord}$ from its vertices to the natural numbers (a linear order) and an assignment $q$ of its edges to queues $\{0, \dots, k-1\}$ such that two edges in the same queue are never nested: for edges $vw$ and $xy$ with $\mathrm{ord}(v) < \mathrm{ord}(x) < \mathrm{ord}(y) < \mathrm{ord}(w)$, $q(vw) \ne q(xy)$. A graph without edges has a $0$-queue layout, provided its vertex set injects into the natural numbers; an edgeless graph on the real numbers has no such layout.
