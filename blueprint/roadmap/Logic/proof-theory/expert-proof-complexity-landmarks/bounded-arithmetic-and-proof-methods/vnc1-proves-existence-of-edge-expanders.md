# Edge expanders exist provably in $VNC^1$

There is a constant $d$ such that the two-sorted theory $VNC^1$ of $NC^1$ reasoning proves that for every $a$ there is a $2d$-regular graph on at least $a$ vertices with edge expansion at least $1/1296$; the graphs come from a combinatorial, eigenvalue-free analysis of an iterated tensor, power and replacement product construction.

Graphs are undirected and may have parallel edges and self-loops, each self-loop at $v$ counting as one edge $v \sim v$. For a $D$-regular graph $G = (V, E)$ and a set $\emptyset \ne U \subsetneq V$ with complement $\overline{U} = V \setminus U$, let $E(U, \overline{U})$ be the set of edges between $U$ and $\overline{U}$ and

$$
\operatorname{edge-exp}_G(U) = \frac{|E(U, \overline{U})|}{D \cdot \min\{|U|, |\overline{U}|\}} .
$$

The **edge expansion** of $G$ is the minimum of $\operatorname{edge-exp}_G(U)$ over all such $U$. A $D$-regular graph is given by its rotation map $\mathrm{Rot}_G(v, i) = (w, j)$, meaning that $w$ is the $i$-th neighbour of $v$ and $v$ is the $j$-th neighbour of $w$.

The theory $V^0$ is two-sorted, with numbers and binary strings $X$ (with length $|X|$ and bits $X(i)$); it has finitely many open BASIC axioms and the comprehension scheme $\exists X \le y \, \forall z < y \, (X(z) \leftrightarrow \varphi(z))$ for every $\Sigma^B_0$ formula $\varphi$ (all number quantifiers bounded, no string quantifiers) not containing $X$ free. The theory $VNC^1$ (in the form of Cook and Morioka) adds, for all $\Sigma^B_0$ formulas $\varphi[p, q]$ and $\psi$, the tree-recursion axiom $\exists Z \le 2a \, B^{\varphi, \psi}(a, \vec{x}, \vec{X}, Z)$, where $B^{\varphi, \psi}$ states that for all $i < a$, $Z(a + i) \leftrightarrow \psi(i)$ and $Z(i) \leftrightarrow \varphi(i, \vec{x}, \vec{X})[Z(2i+1), Z(2i+2)]$; that is, $Z$ evaluates a balanced binary tree of fan-in two gates. The $\Sigma^B_1$-definable functions of $VNC^1$ are exactly the uniform $NC^1$ functions.

**Theorem.** There is a constant $d$ such that $VNC^1$ proves

$$
\forall a \, \exists V, E \, \big[ |V| \ge a \wedge (V, E) \text{ is a degree } 2d \text{ graph} \wedge \forall U \, (U \subseteq V \to \operatorname{edge-exp}_{(V,E)}(U) \ge 1/1296) \big],
$$

where $U$ ranges over nonempty proper subsets. In fact there is a $\Sigma^B_1$-definable function $G$ of $VNC^1$ such that $VNC^1$ proves, for all $a$, that $G(a) = (V, E)$ is a degree $2d$ graph with $|V| \ge a$ and edge expansion at least $1/1296$.

Two refinements are also provable. There are a constant $d = 2^{\ell}$ and a $\Sigma^B_1$-definable function $G$ of $VNC^1$ such that $VNC^1$ proves that for every $a$, $G(a)$ is a $4d$-regular graph on exactly $a$ vertices with edge expansion at least $1/(2 \cdot 1296)$. For every fixed rational $0 < \alpha < 1$ there are $A > 0$ and a $\Sigma^B_1$-defined function $F(m)$ of $VNC^1$ such that $VNC^1$ proves that for every $m$, $F(m)$ is the rotation map of an $(\alpha, A)$ bipartite vertex expander on $m + m$ vertices: a bipartite graph with sides of size $m$ and degree at most $A$ in which, for every $\ell \le m$, every set $S$ of vertices in either side with $|S| \ge \alpha \ell$ has at least $(1 - \alpha)\ell$ neighbours.

## Expansion

The construction is a variant of the Reingold, Vadhan and Wigderson zig-zag iteration. Writing $\bigcirc G$ for $G$ with $d$ extra self-loops at every vertex, $G^k$ for the $k$-th power (edges are walks of length $k$), $G \otimes H$ for the tensor product and $G \circ H$ for the replacement product, one fixes a constant-size $2d$-regular $G_0$ and a $d$-regular $H$ on $(2(4d)^2)^c$ vertices with edge expansion at least $1/3$, both found by exhaustive search, and sets

$$
G_{i+1} = \Big( \bigcirc \big( (\bigcirc G_i) \otimes (\bigcirc G_i) \big) \Big)^{c} \circ H .
$$

Edge expansion is tracked combinatorially: adding self-loops halves it; $(\bigcirc G)^k$ has expansion at least $\tfrac{1}{2}\big(1 - (1 - \epsilon^2/4)^{k/2}\big)$ (via Mihail's combinatorial mixing bound); tensoring graphs with half their degree in self-loops keeps at least $\min\{\epsilon_G, \epsilon_H\}/50$; replacement gives at least $\epsilon_G^2 \epsilon_H / 48$ (Alon, Schwartz and Shapira). With a suitable constant $c$ the power has expansion at least $1/3$, so $G_{i+1}$ has expansion at least $(1/3)^3/48 = 1/1296$, with $|V_{i+1}| = |V_i|^2 (2(4d)^2)^c$.

The rotation map is decidable in alternating time linear in the length of a vertex name, that is, alternating logarithmic time in the graph size, so it lies in uniform $NC^1$. Each expansion lemma has a constructive contrapositive computable in $NC^1$: from a non-expanding set of $G_{i+1}$ it finds one of $G_i$. Because sizes square at each step, this yields a $VNC^1$ proof of $\psi(a) \to \psi(\lfloor \sqrt{a} \rfloor)$ for the $\Sigma^B_1$ statement $\psi$ asserting a small non-expanding set. A conservation result for this telescoping induction then gives $\psi(a) \to \psi(1)$, and $\psi(1)$ is refuted by direct evaluation on the constant graph $G_0$. A variant recursion produces graphs on exactly $2^i$ vertices, and merging vertex pairs gives every size. No eigenvalues or determinants, which are not known to be $NC^1$ computable, are used.

## Depends on

None.

## Proof depends on

None.

## Sources

- Sam Buss, Valentine Kabanets, Antonina Kolokolova, Michal Koucký, "Expander construction in $VNC^1$", *Annals of Pure and Applied Logic*, 2020, doi:10.1016/j.apal.2020.102796 (Theorem 6.8, Theorem 6.9, Theorem 6.10; definitions in Sections 2.2, 2.3 and 5; construction and analysis in Sections 3 and 4; conservation result Theorem 6.3; numbering of the authors' full version dated 7 November 2016, the edition read).
