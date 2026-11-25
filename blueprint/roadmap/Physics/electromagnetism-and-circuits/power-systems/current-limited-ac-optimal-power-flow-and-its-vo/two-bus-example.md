# Two-bus test instance with one unit-conductance branch

The two-bus instance of the [current-limited optimal power flow problem](current-limited-opf.md) has
$n = 2$ buses and $m = 1$ branch, with

- incidence matrix $B = (1, -1)^{\mathsf T}$ and branch admittance $y = 1$, a unit conductance with
  no susceptance;
- no shunt admittances and zero active and reactive demands;
- at both buses, active-generation limits $-2$ and $2$, reactive-generation limits $-1$ and $1$, and
  squared-voltage bounds $1/8$ and $2$;
- squared branch-current limit $4$;
- cost coefficient $1$ at both buses.

Its [bus admittance matrix](admittance.md) is

$$Y = \begin{pmatrix} 1 & -1 \\ -1 & 1 \end{pmatrix}.$$
