# Below threshold the output conductance is zero

For all real $\beta$ and $V_{DS}$ and every $u < 0$, the [square-law drain current](current.md)
$I(\beta, u, V_{DS})$ ($0$ for $u \le 0$, the [triode formula](triode-current.md) for $u > 0$ and
$V_{DS} \le u$, the [saturation formula](saturation-current.md) for $u > 0$ and $V_{DS} > u$) has
derivative $0$ with respect to $V_{DS}$ at $V_{DS}$ ($u$ fixed): the output conductance
$g_{ds} = \partial I / \partial V_{DS}$ vanishes for every $V_{DS}$ when $u < 0$. In the physical
reading $\beta > 0$ is the device constant, $u = V_{GS} - V_{th}$ the gate overdrive and
$V_{DS} \ge 0$ the drain–source voltage of a forward-biased nMOS transistor.
