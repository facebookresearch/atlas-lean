# Process flowsheet with unit holdup balances for each species

Let $U$ be a finite set of process units and $S$ a set of species. A process flowsheet consists of
real-valued functions of time $t \in \mathbb{R}$: the holdup $m_{s,u}(t)$ of species $s$ in unit
$u$, the internal transfer rate $q_{s,i,j}(t)$ of $s$ from unit $i$ to unit $j$, the external inflow
rate $e^{\mathrm{in}}_{s,u}(t)$, the external outflow rate $e^{\mathrm{out}}_{s,u}(t)$ and the
generation rate $g_{s,u}(t)$, together with the unit balances: for every species $s$, unit $u$ and
time $t$, the holdup $m_{s,u}$ is differentiable at $t$ with

$$m_{s,u}'(t) = \sum_{j \in U} \bigl(q_{s,j,u}(t) - q_{s,u,j}(t)\bigr) +
e^{\mathrm{in}}_{s,u}(t) - e^{\mathrm{out}}_{s,u}(t) + g_{s,u}(t).$$

Each internal transfer from $i$ to $j$ appears once as an outflow of $i$ and once as an inflow of
$j$; a self-transfer $q_{s,u,u}$ cancels in its own balance. No sign is imposed on any rate or
holdup: in the physical reading holdups and the inflow, outflow and transfer rates are nonnegative
and generation may have either sign. The balances are assumptions of the structure, not consequences
of a dynamics.
