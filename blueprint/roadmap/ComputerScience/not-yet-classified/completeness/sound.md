# Sound motion planner

A planner is sound if, for every path-planning problem and every step $k$: (1) whenever it reports a path at step $k$, that path solves the problem (it runs from the start to the goal configuration within the free set), and (2) whenever it reports that no path exists, the problem has no solution (LaValle, *Planning Algorithms*, Formulation 4.1 in Section 4.3.1 and the introduction to Chapter 5).
