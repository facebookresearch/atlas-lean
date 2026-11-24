# With zero net supply in every unit, total holdup has zero derivative

Let $F$ be a [process flowsheet](flowsheet.md) over a finite set of units, with holdups
$m_{s,u}(t)$, internal transfer rates $q_{s,i,j}(t)$ from unit $i$ to unit $j$, external inflow
rates $e^{\mathrm{in}}_{s,u}(t)$, external outflow rates $e^{\mathrm{out}}_{s,u}(t)$ and generation
rates $g_{s,u}(t)$, whose unit balances hold for every species, unit and time. Let $s$ be a species
and $t$ a time with $e^{\mathrm{in}}_{s,u}(t) - e^{\mathrm{out}}_{s,u}(t) + g_{s,u}(t) = 0$ for
every unit $u$. Then the total holdup $\sum_{u} m_{s,u}$ has derivative $0$ at $t$. The condition is
at the one time $t$, and so is the conclusion; constancy over an interval would need it at every
time of the interval.
