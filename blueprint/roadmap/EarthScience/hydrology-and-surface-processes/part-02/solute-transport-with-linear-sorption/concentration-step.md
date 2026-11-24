# Explicit concentration step of solute transport in a cell network

Let $V$ be a set of cells and $E$ a finite set of arcs, each arc $e$ running from its tail $t(e)$
to its head $h(e)$. Given real numbers $C_i$ (storage capacities), a time step $\Delta t$, arc flows
$Q_e$, external inflows $q^{\mathrm{in}}_i$ with concentrations $c^{\mathrm{in}}_i$, first-order loss
rates $k_i$ and cell concentrations $c_i$, the concentration of cell $i$ after the step is

$$c'_i = c_i + \frac{\Delta t \Bigl(\sum_{h(e) = i} Q_e \bigl(c_{t(e)} - c_i\bigr) + q^{\mathrm{in}}_i \bigl(c^{\mathrm{in}}_i - c_i\bigr)\Bigr)}{C_i} - \Delta t\, k_i c_i ,$$

where the quotient is read as $0$ when $C_i = 0$. For positive capacities, nonnegative flows and
$\Delta t \ge 0$ this is the explicit step of the mixing form: each inflow, from an arc into $i$ or
from outside, displaces an equal water volume at the cell concentration $c_i$, and the loss acts on
the stored mass.
