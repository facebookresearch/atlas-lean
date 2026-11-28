# Optimum branchings by the super-root reduction

Let $G$ be a digraph with real arc weights $w$. Add a new vertex $\rho$ and an arc of cost $0$ from every original vertex to $\rho$, and turn each original arc $u \to v$ into the arc $v \to u$ with cost $-w(u, v)$. This instance always has a spanning in-arborescence rooted at $\rho$, and deleting the arcs into $\rho$ from a minimum-cost one and reversing the remaining arcs gives a **maximum-weight branching** of $G$, whose weight is minus that cost. This is the reduction of Chekuri (CS 598CSC, Lecture 23, Section 2: a new vertex $r$ with an arc $(r, v)$ of weight $0$ to every vertex $v$, a maximum-weight arborescence rooted at $r$, and Proposition 2 for its existence), with all arcs reversed and weights negated. So Chu-Liu/Edmonds computes a maximum-weight branching of $G$; running it on $-w$ gives a minimum-weight branching.

## Proof sketch

Spanning in-arborescences rooted at $\rho$ correspond bijectively to branchings $B$ of $G$, with cost equal to minus the weight of $B$: a vertex $v$ points either to $\rho$, when no arc of $B$ enters $v$, or to $u$, when $u \to v$ is the arc of $B$ entering $v$; acyclicity of the branching is reachability of $\rho$, and the arcs of all vertices to $\rho$ form an in-arborescence, so one always exists. Hence minimum-cost in-arborescences correspond to maximum-weight branchings. All branchings correspond, not only the optimal ones: for a single arc $u \to v$ of weight $1$ the two branchings $\emptyset$ and $\{u \to v\}$ give the in-arborescences of costs $0$ and $-1$. Arcs of negative weight need not be removed first, as Chekuri does: they give arcs of positive cost that a minimum-cost in-arborescence can replace by the arc to $\rho$, just as an optimum branching contains no arc of negative weight (Edmonds, Section 2).

## Depends on

- [Spanning arborescences and branchings](spanning-arborescences-and-branchings.md)
- [The Chu-Liu/Edmonds algorithm](chu-liu-edmonds-algorithm.md)

## Proof depends on

- [Correctness and optimality of Chu-Liu/Edmonds](chu-liu-edmonds-correctness.md)

## Sources

- C. Chekuri, CS 598CSC Combinatorial Optimization, University of Illinois, Spring 2010, Lecture 23 (April 20, 2010; scribe J. Gao), "Arborescences and Branchings", Section 2, Proposition 2 and "Max-weight arborescences and Branchings": <https://courses.grainger.illinois.edu/cs598csc/sp2010/Lectures/Lecture23.pdf>.
- J. Edmonds, "Optimum Branchings", Journal of Research of the National Bureau of Standards, Section B 71B(4), 1967, Section 2; open copy: <https://nvlpubs.nist.gov/nistpubs/jres/71B/jresv71Bn4p233_A1b.pdf>.
- A. Schrijver, "Combinatorial Optimization: Polyhedra and Efficiency", Springer, 2003.
