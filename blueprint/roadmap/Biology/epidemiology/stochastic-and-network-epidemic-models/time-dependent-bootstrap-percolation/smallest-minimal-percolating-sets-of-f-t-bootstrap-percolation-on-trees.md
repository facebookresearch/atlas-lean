# Smallest minimal percolating sets of $F(t)$-bootstrap percolation on trees

**Model.** For a graph $G=(V,E)$ and a **percolation function** $F:\mathbb{N}\to\mathbb{N}$, $F(t)$-bootstrap percolation started from $A_0\subseteq V$ evolves by

$$A_{t+1}=A_t\cup\{v\in V:\ |N(v)\cap A_t|\ge F(t)\},$$

with final infected set $A_\infty$. It models a pathogen whose transmissibility changes over time by mutation: a node is infected at time $t$ once $F(t)$ neighbors are infected. A motivating choice is $F(t)=\big\lceil 1/\beta(t)\big\rceil$ with $\beta(t)=(b_0-b_f)(1-k)^t+b_f$, $0<k<1$. A **percolating set** satisfies $A_\infty=V$ in finite time; it is **minimal** if no proper subset percolates.

**Results.**
1. *(Reduction to classical thresholds.)* If $F$ attains its minimum $m=\min_tF(t)$ infinitely often, then $F(t)$-bootstrap percolation has the same final set as classical $m$-bootstrap percolation, hence the same critical initial-infection probability.
2. *(Greedy algorithm on trees.)* On a finite rooted tree, the following finds a smallest minimal percolating set in polynomial time. Give every node a latest allowed infection time $t_*(v)=\infty$; repeatedly percolate from the current $A_0$ and stop if everything is infected; otherwise take an unconsidered node $v$ farthest from the root (an isolated one if possible, i.e. one that no single added vertex can infect). If $v$ is isolated or is the root, add it to $A_0$; otherwise lower $t_*(\mathrm{par}(v))$ to $t_p(v)-1$, where $t_p(v)$ is the latest time at which $v$ can still be infected given one more infected neighbor. Mark $v$ considered and repeat.

## Expansion

For item 1, $A_\infty$ is monotone in the threshold, so it is contained in the final set of $m$-bootstrap percolation; conversely any vertex that would become infected under threshold $m$ eventually sees a time with $F(t)=m$ and an unchanged infected neighborhood, so the two final sets coincide. For item 2, leaves cannot be infected by descendants, so the cheapest way to cover a deepest uninfected node is either to seed it or to make its parent infected early enough; propagating deadlines $t_*$ upward and seeding only when forced gives a set that is no larger than any other percolating set. In simulations, exponentially growing percolation functions require much larger minimal percolating sets than polynomial ones.

## Sources

- Yuyuan Luo and Laura P. Schaposnik, "Minimal percolating sets for mutating infectious diseases", arXiv:1911.01988 (2019), Definition 2, Proposition 4 and Theorem 23 (Sections 3 and 6), <https://doi.org/10.48550/arXiv.1911.01988>.
