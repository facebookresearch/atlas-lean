# Two-bus example: the identity is relaxation-feasible but not a lift

For the [two-bus instance](two-bus-example.md), the $2 \times 2$ identity matrix $I_2$ is
[feasible for the semidefinite relaxation](sdp-feasible.md), and $V V^{\mathsf H} \ne I_2$ for every
$V \in \mathbb{C}^2$, so $I_2$ is the [voltage lift](voltage-lift.md) of no voltage vector. The
identity is positive semidefinite of rank two; its active and reactive pairings are $1$ and $0$ at
each bus, its voltage pairings $1$ and its branch-current pairing $2$, all within the limits. It is
not a lift because $W_{12} = V_1 \overline{V_2} = 0$ forces $V_1 = 0$ or $V_2 = 0$, while
$W_{11} = |V_1|^2$ and $W_{22} = |V_2|^2$ must both be $1$.
