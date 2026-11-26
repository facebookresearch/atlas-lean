# Count-to-infinity in distance-vector routing

In distance-vector routing, each node $x$ of a network keeps an estimate $D_x(y) \in \mathbb{N} \cup \{\infty\}$ of its distance to each destination $y$, where $\infty$ means that $x$ knows no route to $y$. In each round, every node recomputes its estimates from the vectors its neighbors held before the round: $D_x(x) = 0$ and, for $y \ne x$, $D_x(y) = \min_v \bigl(c(x, v) + D_v(y)\bigr)$ over its neighbors $v$, where $c(x, v) \in \mathbb{N}$ is the cost of the link from $x$ to $v$ and the minimum over no neighbors is $\infty$. Advertisements carry only distances, not paths.

**Theorem.** Take the path network $A - B - C$ with $c(A, B) = c(B, A) = 1$ and $c(B, C) = 2$, and estimates with $D_A(C) = 3$, $D_B(C) = 2$ and $D_C(C) = 0$, the others arbitrary, so that $A$ routes to $C$ through $B$, its only neighbor. A round leaves these estimates of the distance to $C$ unchanged. Suppose the link $B - C$ fails. The advertisement $D_A(C) = 3$ is implicitly a path through $B$ itself, but $B$ cannot tell this and accepts it:

- in the first round, $B$ sets $D_B(C) = 1 + 3 = 4$;
- in the second, $A$ sets $D_A(C) = 1 + 4 = 5$;
- in the third, $B$ sets $D_B(C) = 6$, and so on.

After $k$ rounds, $D_A(C) = 3 + 2 \lfloor k/2 \rfloor$ and $D_B(C) = 2 + 2 \lceil k/2 \rceil$: in each round one of the two estimates increases by $2$, alternately that of $B$ and that of $A$. Both estimates remain finite and increase without bound: for every $n$ there is a $k$ such that after $k$ rounds both exceed $n$.

## Sources

- A. C. Snoeren, *Distance-vector Routing*, Lecture 13 of CSE 123: Computer Networks, UC San Diego, Fall 2010, <https://cseweb.ucsd.edu/classes/fa10/cse123/lectures/123-fa10-l13.pdf>: the update rule on slide 5, the "Counting to Infinity" example on slide 13 (distances to $C$ of $3$ and $2$, then updates $4$, $5$, …), and "Why so High?" on slide 14.
- J. F. Kurose and K. W. Ross, *Computer Networking: A Top-Down Approach*, 8th ed., Pearson, 2021, Section 5.2.2.
