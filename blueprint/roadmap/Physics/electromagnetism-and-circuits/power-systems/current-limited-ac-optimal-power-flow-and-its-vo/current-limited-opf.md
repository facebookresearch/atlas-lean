# Data of a current-limited AC optimal power flow problem

For natural numbers $n$ (buses) and $m$ (branches), an instance of the current-limited AC optimal
power flow problem, with one aggregate generator per bus, consists of:

- a real matrix $B \in \mathbb{R}^{n \times m}$, the signed node–branch incidence matrix;
- branch admittances $y \in \mathbb{C}^m$ and shunt admittances $y^{\mathrm{sh}} \in \mathbb{C}^n$;
- fixed active and reactive demands $P^d_k, Q^d_k \in \mathbb{R}$ at each bus $k$;
- lower and upper limits $P^{\min}_k, P^{\max}_k$ on the active generation and
  $Q^{\min}_k, Q^{\max}_k$ on the reactive generation at each bus $k$;
- lower and upper bounds $v^{\min}_k, v^{\max}_k$ on the squared voltage magnitude at each bus $k$;
- an upper bound $i^{\max}_e$ on the squared current magnitude on each branch $e$;
- a cost coefficient $c_k \in \mathbb{R}$ of active generation at each bus $k$.

No condition relates these numbers: the entries of $B$ are arbitrary reals, the admittances
arbitrary complex numbers, and a lower limit may exceed the corresponding upper limit, in which case
no voltage vector is feasible. In the physical reading $B$ has one entry $1$ and one entry $-1$ in
each column, the admittances have nonnegative real parts, the limits are ordered and the
squared-magnitude bounds are nonnegative. The instance determines its
[bus admittance matrix](admittance.md), its [AC feasibility](ac-feasible.md) and [cost](ac-cost.md),
and its [semidefinite relaxation](sdp-feasible.md).
