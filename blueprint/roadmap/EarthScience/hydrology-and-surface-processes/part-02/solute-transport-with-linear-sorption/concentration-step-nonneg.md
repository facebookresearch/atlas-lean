# Nonnegativity of the concentration step

Let $V$ be a finite set of cells and $E$ a finite set of arcs, each arc $e$ running from its tail $t(e)$ to its head $h(e)$, and write $(Bf)_i = \sum_{h(e) = i} f_e - \sum_{t(e) = i} f_e$ for the net arc inflow of an arc quantity $f$ at cell $i$. Suppose that the capacities satisfy $C_i > 0$, the time step $\Delta t \ge 0$, and
the arc flows, external inflows, inflow concentrations and concentrations are nonnegative:
$Q_e \ge 0$, $q^{\mathrm{in}}_i \ge 0$, $c^{\mathrm{in}}_i \ge 0$ and $c_i \ge 0$. Suppose that the
carrier-water balance $(BQ)_i + q^{\mathrm{in}}_i = q^{\mathrm{out}}_i$ holds and that every cell
satisfies the budget

$$\sum_{t(e) = i} \frac{\Delta t\, Q_e}{C_{t(e)}} + \Delta t \Bigl(\frac{q^{\mathrm{out}}_i}{C_i} + k_i\Bigr) \le 1 .$$

Then the explicit concentration step $c'_i = c_i + \Delta t \bigl(\sum_{h(e) = i} Q_e (c_{t(e)} - c_i) + q^{\mathrm{in}}_i (c^{\mathrm{in}}_i - c_i)\bigr) / C_i - \Delta t\, k_i c_i$ satisfies $C_i c'_i \ge 0$ and $c'_i \ge 0$ for every cell $i$. No sign is
assumed for the outflows $q^{\mathrm{out}}$ or the loss rates $k$ beyond the budget.
