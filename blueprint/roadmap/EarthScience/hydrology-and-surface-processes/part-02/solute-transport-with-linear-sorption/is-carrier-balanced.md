# Carrier-water balance of a cell network

Let $V$ be a finite set of cells and $E$ a finite set of arcs, each arc $e$ running from its tail $t(e)$ to its head $h(e)$, and write $(Bf)_i = \sum_{h(e) = i} f_e - \sum_{t(e) = i} f_e$ for the net arc inflow of an arc quantity $f$ at cell $i$. Arc flows $Q \in \mathbb{R}^E$, external inflows $q^{\mathrm{in}} \in \mathbb{R}^V$ and
external outflows $q^{\mathrm{out}} \in \mathbb{R}^V$ satisfy the carrier-water balance when
$(BQ)_i + q^{\mathrm{in}}_i = q^{\mathrm{out}}_i$ for every cell $i$: the net arc inflow plus the
external inflow equals the external outflow, so the carrier-water volume of every cell stays fixed.
