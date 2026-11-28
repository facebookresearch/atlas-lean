# Near-minimum cuts, atoms and polygon representations of a Held-Karp point

Let $G=(V,E,x)$ be a graph with weights $x \ge 0$ and a distinguished edge $e_0=u_0v_0$, such that $x(\delta(S)) \ge 2$ for every $S \subseteq V \setminus\{u_0,v_0\}$, $S \ne \emptyset$ (as obtained from a subtour LP solution by splitting one vertex). For $\eta \ge 0$ such a set $S$ is an $\eta$-near minimum cut if $x(\delta(S)) \le 2+\eta$. Two cuts $S,S'$ cross if $S \cap S'$, $S \setminus S'$, $S' \setminus S$ and $V \setminus (S \cup S')$ are all nonempty. For a connected component $\mathcal{C}$ of the crossing graph on $\eta$-near minimum cuts, the atoms $a_0,\dots,a_{k-1}$ form the coarsest partition of $V$ such that each atom lies on one side of every cut in $\mathcal{C}$, with $u_0,v_0 \in a_0$. A polygon representation places the atoms on the sides of a regular polygon or in its interior so that every cut in $\mathcal{C}$ is the union of the atoms on one side of some diagonal; Benczur and Goemans proved one exists whenever $\eta < 2/5$, that is, for cuts of value less than $6/5$ of the minimum cut value $2$. For $\eta=0$ and a component $\mathcal{C}$ containing at least two (hence crossing) cuts, this is the cactus structure: the atoms lie around a cycle with $x(E(a_i,a_{i+1}))=1$ for cyclically consecutive atoms. A component consisting of a single cut $S$, crossed by no other near minimum cut, is treated separately: its atoms are $S$ and $V \setminus S$, and the weight between them is $x(\delta(S)) \in [2, 2+\eta]$, not $1$. For example, in a triangle with unit weights and distinguished edge $u_0v_0$, the only eligible shore is $\{w\}$ for the third vertex $w$, and the weight between its two atoms is $2$.

## Depends on

- [Subtour elimination LP of a metric TSP instance](subtour-elimination-lp.md)
- [Cut capacity](../../../../GraphTheory/matchings-and-flows/max-flow-min-cut-theorem/cut-capacity.md)

## Sources

- Andras A. Benczur, Michel X. Goemans, "Deformable Polygon Representation and Near-Mincuts", Building Bridges, Bolyai Society Mathematical Studies 19 (2008).
- Efim A. Dinits, Alexander V. Karzanov, Michael V. Lomonosov, "On the Structure of a Family of Minimal Weighted Cuts in a Graph", Studies in Discrete Optimization (1976).
- Anna R. Karlin, Nathan Klein, Shayan Oveis Gharan, "A (Slightly) Improved Approximation Algorithm for Metric TSP", STOC (2021), arXiv:2007.01409, Sections 1.2.1, 2.1, 2.3 and 4.5.
