# Total stored mass after a concentration step

Let $V$ be a finite set of cells and $E$ a finite set of arcs, each arc $e$ running from its tail $t(e)$ to its head $h(e)$, and write $(Bf)_i = \sum_{h(e) = i} f_e - \sum_{t(e) = i} f_e$ for the net arc inflow of an arc quantity $f$ at cell $i$. Let $C_i \neq 0$ be storage capacities, and suppose that arc flows $Q$, external
inflows $q^{\mathrm{in}}$ and external outflows $q^{\mathrm{out}}$ satisfy the carrier-water balance
$(BQ)_i + q^{\mathrm{in}}_i = q^{\mathrm{out}}_i$ for every $i$. Then for every time step
$\Delta t$, inflow concentrations $c^{\mathrm{in}}$, loss rates $k$ and concentrations $c$,
the explicit concentration step $c'_i = c_i + \Delta t \bigl(\sum_{h(e) = i} Q_e (c_{t(e)} - c_i) + q^{\mathrm{in}}_i (c^{\mathrm{in}}_i - c_i)\bigr) / C_i - \Delta t\, k_i c_i$ satisfies

$$\sum_i C_i c'_i = \sum_i C_i c_i + \sum_i \Delta t\, q^{\mathrm{in}}_i c^{\mathrm{in}}_i - \sum_i \Delta t \Bigl(\frac{q^{\mathrm{out}}_i}{C_i} + k_i\Bigr) C_i c_i :$$

the arc transfers cancel, and the total stored mass changes only by the external source and the
retirement.
