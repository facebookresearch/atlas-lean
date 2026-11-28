# Polygons of near-minimum cuts crossed on one side (Karlin-Klein-Oveis Gharan)

There are absolute constants $\eta_0 > 0$ and $C$ (Theorem 4.9 of Karlin–Klein–Oveis Gharan allows any error $\epsilon_\eta \ge 14\eta$, i.e. $C=14$) such that the following holds for $0 \le \eta \le \eta_0$. Let $\mathcal{C}$ be a connected component of crossing $\eta$-near minimum cuts of $G=(V,E,x)$ with a polygon representation in which no atom lies inside the polygon, and such that, identifying each cut with the interval of polygon atoms not containing $a_0$, every interval is crossed only on its left or only on its right. Then for every atom $a_i$, the root $a_0$ included, and every pair of cyclically consecutive atoms, $(a_{m-1}, a_0)$ included,

$$
x(\delta(a_i)) \le 2+C\eta \qquad\text{and}\qquad x(E(a_i,a_{i+1})) \ge 1-C\eta .
$$

## Proof sketch

Charge each atom to the near minimum cuts formed by consecutive intervals around it and apply submodularity of $S \mapsto x(\delta(S))$ to pairs of crossing intervals, which forces their intersections and differences to be near minimum as well. The one-sided crossing hypothesis lets the intervals be ordered so that each atom is the difference of two nested near-minimum intervals, giving $x(\delta(a_i)) \le 2+O(\eta)$. Comparing an interval with its extension by one atom then shows that almost one unit of weight runs between neighbouring atoms.

## Depends on

- [Near-minimum cuts, atoms and polygon representations of a Held-Karp point](near-min-cuts-polygon.md)

## Sources

- Anna R. Karlin, Nathan Klein, Shayan Oveis Gharan, "A (Slightly) Improved Approximation Algorithm for Metric TSP", STOC (2021), arXiv:2007.01409, Section 1.2.1 and Section 4.3 (Definition 4.8, Theorem 4.9).
- Andras A. Benczur, Michel X. Goemans, "Deformable Polygon Representation and Near-Mincuts", Building Bridges, Bolyai Society Mathematical Studies 19 (2008).
