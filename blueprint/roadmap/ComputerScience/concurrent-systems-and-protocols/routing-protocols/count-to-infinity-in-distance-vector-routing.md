# Count-to-infinity in distance-vector routing

In distance-vector routing, each node $x$ keeps an estimate $D_x(y)$ of its distance to each destination $y$. It recomputes $D_x(y) = \min_v \bigl(c(x, v) + D_v(y)\bigr)$ over its neighbors $v$ from the vectors they advertise, and advertises its own vector when it changes. Advertisements carry only distances, not paths.

**Count-to-infinity.** Without further mechanisms, bad news can propagate arbitrarily slowly. Take the path network $A - B - C$ with $c(A, B) = 1$ and $c(B, C) = 2$, so that $D_A(C) = 3$ and $D_B(C) = 2$, with $A$ routing through $B$. Suppose the link $B - C$ fails. The advertisement $D_A(C) = 3$ is implicitly a path through $B$ itself, but $B$ cannot tell this and accepts it:
- $B$ sets $D_B(C) = 1 + 3 = 4$;
- $A$ then sets $D_A(C) = 1 + 4 = 5$;
- $B$ sets $D_B(C) = 6$, and so on.

The estimates increase by $2$ per exchange without bound. They stop only when a fixed "infinity" bound is reached, such as $16$ hops in RIP. Even where the estimates do not diverge, for example when an alternative path of large cost exists, the same effect delays convergence.

**Mitigations.**
- *Split horizon:* a node never advertises a destination to the neighbor that is its next hop for it.
- *Poison reverse:* it advertises that destination to its next hop with metric $\infty$.

Either rule prevents the two-node loop above, but neither prevents loops of three or more nodes. Hold-down timers and path information in advertisements are other mitigations.

## Sources

- A. C. Snoeren, *Distance-vector Routing*, Lecture 13 of CSE 123: Computer Networks, UC San Diego, Fall 2010, <https://cseweb.ucsd.edu/classes/fa10/cse123/lectures/123-fa10-l13.pdf>: the "Counting to Infinity" example on slide 13 (distances to $C$ of $3$ and $2$, then updates $4$, $5$, …), "Why so High?" on slide 14, the mitigation strategies on slide 15 (hold-downs, loop avoidance, split horizon, poison reverse and its limitation to loops of size 2), and RIP's infinity of 16 hops.
- J. F. Kurose and K. W. Ross, *Computer Networking: A Top-Down Approach*, 8th ed., Pearson, 2021, Section 5.2.2.
