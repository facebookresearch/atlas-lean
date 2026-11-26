# Polygons of near-minimum cuts crossed on one side (Karlin-Klein-Oveis Gharan)

There are absolute constants $\eta_0 > 0$ and $C$ such that the following holds for $0 \le \eta \le \eta_0$. Let $\mathcal{C}$ be a connected component of crossing $\eta$-near minimum cuts of $G=(V,E,x)$ with a polygon representation in which no atom lies inside the polygon, and such that, identifying each cut with the interval of polygon atoms not containing $a_0$, every interval is crossed only on its left or only on its right. Then for every atom $a_i$ with $i \ne 0$ and every pair of consecutive atoms,

$$
x(\delta(a_i)) \le 2+C\eta \qquad\text{and}\qquad x(E(a_i,a_{i+1})) \ge 1-C\eta .
$$

## Proof sketch

Charge each atom to the near minimum cuts formed by consecutive intervals around it and apply submodularity of $S \mapsto x(\delta(S))$ to pairs of crossing intervals, which forces their intersections and differences to be near minimum as well. The one-sided crossing hypothesis lets the intervals be ordered so that each atom is the difference of two nested near-minimum intervals, giving $x(\delta(a_i)) \le 2+O(\eta)$. Comparing an interval with its extension by one atom then shows that almost one unit of weight runs between neighbouring atoms.

## Depends on

- [Near-minimum cuts, atoms and polygon representations of a Held-Karp point](near-min-cuts-polygon.md)

## Sources

- Anna R. Karlin, Nathan Klein, Shayan Oveis Gharan, "A (Slightly) Improved Approximation Algorithm for Metric TSP", STOC (2021), arXiv:2007.01409.
- Andras A. Benczur, Michel X. Goemans, "Deformable Polygon Representation and Near-Mincuts", Building Bridges, Bolyai Society Mathematical Studies 19 (2008).
