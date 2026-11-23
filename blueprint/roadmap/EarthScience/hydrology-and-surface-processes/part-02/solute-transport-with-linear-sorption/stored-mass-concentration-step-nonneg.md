# Nonnegative stored mass after a concentration step with linear sorption

Let $V$ be a finite set of cells and $E$ a finite set of arcs, each arc $e$ running from its tail $t(e)$ to its head $h(e)$, and write $(Bf)_i = \sum_{h(e) = i} f_e - \sum_{t(e) = i} f_e$ for the net arc inflow of an arc quantity $f$ at cell $i$. Each cell $i$ has bulk volume $V_i > 0$, porosity $\phi_i > 0$, bulk density
$\rho_{b,i} \ge 0$ and distribution coefficient $K_{d,i} \ge 0$, so that a concentration $c$ stores
the mass $V_i (\phi_i + \rho_{b,i} K_{d,i})\, c$; let $C_i = V_i (\phi_i + \rho_{b,i} K_{d,i})$.
Suppose that $\Delta t \ge 0$, $Q_e \ge 0$, $q^{\mathrm{in}}_i \ge 0$, $c^{\mathrm{in}}_i \ge 0$
and $c_i \ge 0$, that the carrier-water balance $(BQ)_i + q^{\mathrm{in}}_i = q^{\mathrm{out}}_i$
holds, and that every cell satisfies the budget
$\sum_{t(e) = i} \Delta t\, Q_e / C_{t(e)} + \Delta t (q^{\mathrm{out}}_i / C_i + k_i) \le 1$.
Then the concentration after the explicit step with these capacities,
$c'_i = c_i + \Delta t \bigl(\sum_{h(e) = i} Q_e (c_{t(e)} - c_i) + q^{\mathrm{in}}_i
(c^{\mathrm{in}}_i - c_i)\bigr) / C_i - \Delta t\, k_i c_i$, and the stored mass
$V_i (\phi_i + \rho_{b,i} K_{d,i})\, c'_i$ are nonnegative for every cell $i$.
