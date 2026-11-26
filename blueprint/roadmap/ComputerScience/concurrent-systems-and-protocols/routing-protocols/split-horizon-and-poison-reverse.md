# Split horizon and poison reverse in distance-vector routing

Consider distance-vector routing in rounds, as in the [distance-vector round](step.md), modified as follows. Each node $x$ also records, for each destination $y \ne x$ with $D_x(y) < \infty$, a next hop $n_x(y)$: a neighbor $v$ attaining the minimum by which $x$ computed $D_x(y)$, any one if several do. Under *split horizon*, a node $v$ never advertises a destination $y$ to its next hop $n_v(y)$; under *poison reverse*, it advertises $y$ to $n_v(y)$ with the estimate $\infty$. A node keeps no advertisement from an earlier round, so under either rule node $x$ sets $D_x(x) = 0$ and computes, for $y \ne x$,

$$D_x(y) = \min_v \bigl(c(x, v) + \hat D_{v \to x}(y)\bigr), \qquad \hat D_{v \to x}(y) = \begin{cases} \infty & \text{if } n_v(y) = x, \\ D_v(y) & \text{otherwise,} \end{cases}$$

over its neighbors $v$, where $D_v$ and $n_v$ are those of the previous round.

**Theorem.** Under split horizon or poison reverse:

1. Take the path network $A - B - C$ with $c(A, B) = c(B, A) = 1$ and $c(B, C) = 2$, the example of [count-to-infinity](count-to-infinity-in-distance-vector-routing.md), starting from $D_A(C) = 3$ with $n_A(C) = B$ and $D_B(C) = 2$ with $n_B(C) = C$. After the link $B - C$ fails, $D_B(C) = \infty$ after one round, and $D_A(C) = D_B(C) = \infty$ after every later round.
2. Let $A$, $B$ and $C$ be pairwise linked with cost $1$ and let a fourth node $Z$ be linked to $A$ with cost $1$, starting from the distances to $Z$: $D_A(Z) = 1$ with $n_A(Z) = Z$, and $D_B(Z) = D_C(Z) = 2$ with $n_B(Z) = n_C(Z) = A$. After the link $A - Z$ fails, whichever minimizing neighbors are chosen as next hops, for every $k \ge 3$ exactly one of $A$, $B$ and $C$ has a finite estimate of its distance to $Z$ after $k$ rounds, and that estimate is $k + 1$.

So either rule stops the count to infinity of a loop of two nodes, but in the second network the estimates still increase without bound around the loop $A$, $B$, $C$ of three nodes.

## Depends on

- [Distance-vector round](step.md)

## Sources

- A. C. Snoeren, *Distance-vector Routing*, Lecture 13 of CSE 123: Computer Networks, UC San Diego, Fall 2010, <https://cseweb.ucsd.edu/classes/fa10/cse123/lectures/123-fa10-l13.pdf>: split horizon and poison reverse on slide 15 ("A doesn't advertise C to B", "A advertises C to B with a metric of ∞", "Only works for 'loop's of size 2"), and "Split Horizon Limitations" on slide 17, the second network with its fourth node called $D$.
