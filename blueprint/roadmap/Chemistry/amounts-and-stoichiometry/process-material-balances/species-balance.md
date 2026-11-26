# Total holdup changes only through external flows and generation

Let $F$ be a [process flowsheet](flowsheet.md) over a finite set of units, with holdups
$m_{s,u}(t)$, internal transfer rates $q_{s,i,j}(t)$ from unit $i$ to unit $j$, external inflow
rates $e^{\mathrm{in}}_{s,u}(t)$, external outflow rates $e^{\mathrm{out}}_{s,u}(t)$ and generation
rates $g_{s,u}(t)$, whose unit balances hold for every species, unit and time. Then for every
species $s$ and time $t$ the total holdup $M_s(t) = \sum_{u \in U} m_{s,u}(t)$ is differentiable at
$t$ with

$$M_s'(t) = \sum_{u \in U} \bigl(e^{\mathrm{in}}_{s,u}(t) - e^{\mathrm{out}}_{s,u}(t) +
g_{s,u}(t)\bigr):$$

every internal transfer cancels. It is a special case of the
[derivative of the total stock of a box model](../../../EarthScience/geochemistry-and-biogeochemical-cycles/box-models-with-internal-transfers/has-deriv-at-total-stock.md),
with the external source of unit $u$ taken as
$e^{\mathrm{in}}_{s,u} - e^{\mathrm{out}}_{s,u} + g_{s,u}$.
