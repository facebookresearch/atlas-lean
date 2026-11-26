# No dispute wheel implies a unique solution

If an instance of the [stable paths problem](the-stable-paths-problem.md) has no [dispute wheel](dispute-wheels.md), then it has exactly one solution. DISAGREE, with its two solutions, has a dispute wheel of size $2$.

**Proof idea.** Existence is [the previous theorem](no-dispute-wheel-implies-solvability.md). Given two distinct solutions, take the component $T$ containing the origin of the intersection of their trees. Some edge of one tree enters $T$ from a node $u_0$ outside it; following, alternately in the two trees, the paths from such nodes into $T$ yields nodes $u_i$ with spokes $Q_i$ in $T$ and rim paths $R_i$ outside it, and stability of the two solutions gives $\lambda^{u_i}((u_i\,v_i)Q_i) \le \lambda^{u_i}(R_i(u_{i+1}\,v_{i+1})Q_{i+1})$, a dispute wheel.

## Depends on

- [The stable paths problem](the-stable-paths-problem.md)
- [Dispute wheels](dispute-wheels.md)

## Proof depends on

- [No dispute wheel implies solvability](no-dispute-wheel-implies-solvability.md)

## Sources

- T. G. Griffin, F. B. Shepherd and G. Wilfong, "The stable paths problem and interdomain routing", *IEEE/ACM Transactions on Networking* 10(2):232–243, 2002, Section V.D, Theorem V.4 with its proof (Fig. 10).
