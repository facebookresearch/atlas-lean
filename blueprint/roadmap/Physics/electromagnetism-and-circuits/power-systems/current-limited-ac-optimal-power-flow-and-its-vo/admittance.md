# Bus admittance matrix of an optimal power flow instance

For an [instance](current-limited-opf.md) of the current-limited optimal power flow problem with
incidence matrix $B$, branch admittances $y$ and shunt admittances $y^{\mathrm{sh}}$, its bus
admittance matrix is the [bus admittance matrix](bus-admittance.md) of these data,

$$Y = B\, \mathrm{diag}(y)\, B^{\mathsf T} + \mathrm{diag}(y^{\mathrm{sh}}).$$
