# Clique–coloring formulas

For $n, k, r \ge 1$ the clique–coloring formula has shared variables $p_{uv}$ for the possible edges of a graph on $n$ vertices. The clique part $\mathrm{Clique}_{n,k}(p,q)$ has variables $q_{\ell, i}$ ($\ell \in [k]$, $i \in [n]$, "the $\ell$-th member of the clique is vertex $i$") with clauses saying that every member is some vertex, distinct members are distinct vertices, and distinct members are adjacent ($\neg q_{\ell,i} \vee \neg q_{\ell',j} \vee p_{ij}$). The coloring part $\mathrm{Color}_{n,r}(p, z)$ has variables $z_{i,c}$ with clauses saying every vertex gets a color, at most one color, and adjacent vertices get different colors ($\neg p_{ij} \vee \neg z_{i,c} \vee \neg z_{j,c}$). The shared variables occur only positively in the clique part.

## Depends on

- [Interpolants of split CNF formulas](interpolants-of-split-cnf-formulas.md)

## Sources

- J. Krajíček, "Interpolation Theorems, Lower Bounds for Proof Systems, and Independence Results for Bounded Arithmetic", The Journal of Symbolic Logic 62(2), 457–486, 1997: Definition 7.1.
- P. Pudlák, "Lower Bounds for Resolution and Cutting Plane Proofs and Monotone Computations", The Journal of Symbolic Logic 62(3), 981–998, 1997.
