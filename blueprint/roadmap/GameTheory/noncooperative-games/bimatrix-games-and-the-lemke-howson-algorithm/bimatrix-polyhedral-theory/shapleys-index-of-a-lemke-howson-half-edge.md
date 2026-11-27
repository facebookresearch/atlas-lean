# Shapley's index of a Lemke–Howson half-edge

Consider the Lemke–Howson graph with missing label $k_0$ of two nondegenerate bounded systems $A_1 x \le b_1$ in $\mathbb{R}^{n_1}$ and $A_2 y \le b_2$ in $\mathbb{R}^{n_2}$, and fix a linear order on the label set $K$. For a vertex $x$ of the first polyhedron let $K_1(x)$ be its $n_1$ labels and $M_1(x)$ the $n_1 \times n_1$ matrix of the corresponding rows of $A_1$, listed in increasing label order; define $K_2(y)$ and $M_2(y)$ in the same way. A half-edge at a node $(x, y)$ drops a label $\ell$ from one of the two vertices: $\ell$ is the duplicate label of a node that is not completely labelled, and $\ell = k_0$ at a completely labelled pair. List $K_1(x)$ in increasing order followed by $K_2(y)$ in increasing order, and replace $\ell$ by $k_0$ in the list of the vertex from which $\ell$ is dropped (no change when $\ell = k_0$). The result lists every label of $K$ exactly once, so it is a permutation $\pi$ of $K$ relative to its order, and the *sign* of the half-edge is

$$
\operatorname{sgn}(\pi)\,\operatorname{sgn}\det M_1(x)\,\operatorname{sgn}\det M_2(y) \in \{-1, +1\}.
$$

Now let $(A, B)$ be a nondegenerate $m \times n$ bimatrix game with positive payoff matrices, and take its best response polytopes $P$ and $Q$ written with rows $-e_i^\top$ (label $i \in M$) and $(B^\top)_j$ (label $j \in N$) for $P$, and rows $A_i$ (label $i$) and $-e_j^\top$ (label $j$) for $Q$, the labels ordered with $M$ before $N$, each in index order. The *index* of a completely labelled pair $(x, y)$ with supports $L$ of $x$ and $J$ of $y$ (so $|L| = |J|$) is

$$
(-1)^{|L|+1} \operatorname{sgn}\bigl(\det A_{LJ} \det B_{LJ}\bigr),
$$

where $A_{LJ}$ and $B_{LJ}$ are the submatrices with rows $L$ and columns $J$ (von Schemde and von Stengel, Definition 1, Shapley's index of the equilibrium). The artificial equilibrium $(0, 0)$ ($L = J = \emptyset$, empty determinants equal to $1$) has index $-1$.

## Proof sketch

The following identity between the two signs is derived here and stated by none of the sources read: at every completely labelled pair $(x, y)$ of the best response polytopes, the sign of its half-edge times $(-1)^{m+n+1}$ equals its index. It was checked by exact rational computation on all $574$ completely labelled pairs of $273$ random nondegenerate games with positive integer payoffs up to $3 \times 3$, the artificial equilibria included; at $(0, 0)$ both sides are $-1$, since there $K_1(0) = M$, $K_2(0) = N$, $M_1(0) = -I_m$, $M_2(0) = -I_n$ and $\pi$ is the identity, so the half-edge has sign $(-1)^{m+n}$.

## Depends on

- [Lemke–Howson graph of two labelled polyhedra](lemke-howson-graph-of-two-labelled-polyhedra.md)
- [Best response polytopes of a bimatrix game](best-response-polytopes-of-a-bimatrix-game.md)

## Sources

- Lloyd S. Shapley, "A Note on the Lemke–Howson Algorithm", Pivoting and Extensions, Springer Berlin Heidelberg, 1974.
- Bernhard von Stengel, "Equilibrium Computation for Two-Player Games in Strategic and Extensive Form", Algorithmic Game Theory, Cambridge University Press, 2007.
- Arndt von Schemde and Bernhard von Stengel, "Strategic Characterization of the Index of an Equilibrium", Algorithmic Game Theory (SAGT 2008), Lecture Notes in Computer Science 4997, Springer, 2008, Definition 1.
