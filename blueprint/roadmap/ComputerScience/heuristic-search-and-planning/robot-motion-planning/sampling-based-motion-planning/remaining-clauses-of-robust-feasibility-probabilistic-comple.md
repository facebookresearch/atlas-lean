# Goal regions, robust optimality and asymptotic optimality for sampling planners

Robust feasibility of a path problem and probabilistic completeness of a random planner, for point goals, are separate
definitions and are not part of this node. This node collects the remaining clauses.

## Expansion

A sound expansion has separate pages for:

1. **Goal regions.** The bridge from point goals to goal regions of positive measure, with the clearance condition at the goal.
2. **Robust optimality.** Karaman and Frazzoli's robustly optimal solutions (an optimal path with weak $\delta$-clearance whose
   cost is the limit of the costs of every sequence of collision-free paths converging to it in bounded-variation norm) and
   the robust optimum of Solovey et al. (the infimum of the cost over paths with positive clearance), for path length or a
   monotone cost bounded by a constant times total variation.
3. **Asymptotic optimality:** almost sure convergence of the returned cost to the optimum (Karaman and Frazzoli,
   Definition 24) versus convergence in probability to within a factor $1 + \varepsilon$ (Solovey et al., Theorem 1), as distinct
   notions, each with the planners it applies to.

## Sources

- Sampling-based Algorithms for Optimal Motion Planning — S. Karaman, E. Frazzoli, Sec. 2.1 (paths and cost assumptions); Sec. 4.1 (strong $\delta$-clearance, robust feasibility, Definition 14, Theorems 15–17); Sec. 4.2 (robustly optimal solutions, Definition 24). <https://people.eecs.berkeley.edu/~pabbeel/cs287-fa15/optreadings/rrtstar.pdf>
- Stanford CS326 (2009) Class #6: Sampling-Based Motion Planning: Probabilistic Roadmaps — J.-C. Latombe, Stanford University CS326 graduate reading list. <http://ai.stanford.edu/~latombe/cs326/2009/class5/class5.htm>
- Revisiting the Asymptotic Optimality of RRT* — K. Solovey, L. Janson, E. Schmerling, E. Frazzoli, M. Pavone, ICRA 2020. <https://par.nsf.gov/servlets/purl/10192531> Sec. II, Definitions 2 and 3 (robust paths, robust optimum); Sec. IV, Theorem 1.
