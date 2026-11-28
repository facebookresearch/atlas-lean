# Generalized arc consistency of REGULAR by a layered graph

Pesant's propagator for REGULAR unfolds the automaton into $n+1$ layers of states; solutions are the paths from the start state in the first layer to an accepting state in the last, so a forward and a backward reachability pass enforce generalized arc consistency in $O(n|T||Q|)$ time.

Let $M=(Q,T,\delta,q_0,F)$ be a deterministic finite automaton with a nonempty alphabet $T=\{1,\dots,|T|\}$ (as on the [GRAMMAR and REGULAR constraints](grammar-constraint.md) page; $\delta$ may be partial, and the run on a word is defined when every transition it uses is defined), and let $X_1,\dots,X_n$, $n\ge1$, be distinct variables with $D(X_i)\subseteq T$. Assume constant-time evaluation of $\delta$ and of membership in each $D(X_i)$.

*The layered graph $R$.* Its vertices are $n+1$ copies of the states, $q^i$ for $q\in Q$ and $1\le i\le n+1$; for each $i\le n$, each $q\in Q$ and each $a\in D(X_i)$ with $\delta(q,a)$ defined it has an arc from $q^i$ to $\delta(q,a)^{\,i+1}$ labelled $a$. Arcs are identified by their labels, so two labels with the same successor give two parallel arcs.

**Theorem.**

1. The solutions of $\mathrm{REGULAR}(M,[X_1,\dots,X_n])$ correspond one-to-one to the paths in $R$ from $q_0^1$ to a vertex $f^{n+1}$ with $f\in F$, the solution being the sequence of arc labels.
2. The constraint is [generalized arc consistent](../generalized-arc-consistency.md) iff for every $i$ and every $a\in D(X_i)$ some arc of layer $i$ labelled $a$ lies on such a path.
3. Hence GAC is enforced by building $R$ while keeping only arcs reachable from $q_0^1$ (forward pass), removing arcs from which no accepting vertex of layer $n+1$ is reachable (backward pass), and keeping in $D(X_i)$ exactly the labels of surviving arcs of layer $i$; this takes $O(n|T||Q|)$ time and space, and fails exactly when no arc survives.

## Depends on

- [GRAMMAR and REGULAR constraints](grammar-constraint.md): the REGULAR constraint and deterministic finite automata.
- [Generalized arc consistency](../generalized-arc-consistency.md): the consistency enforced.

## Proof depends on

- [Linear bound on the cost of BFS with parents](../../../../ComputerScience/graph-algorithms/traversal-and-connectivity/breadth-first-search/bfs-with-parents-time-le.md): the forward and backward passes of item 3.

## Expansion

*Item 1.* Since $M$ is deterministic, a word $a_1\cdots a_n$ with $a_i\in D(X_i)$ whose run is defined determines a unique path in $R$ from $q_0^1$, through the layer copies of the states of its run, and the path ends in an accepting copy iff $M$ accepts the word; a word whose run is undefined is rejected and has no such path. Conversely every path from $q_0^1$ to layer $n+1$ spells the word read along its labels.

*Item 2* follows: a value $a\in D(X_i)$ has a support iff some accepted word in the product of the domains has $a$ in position $i$, iff some accepting path uses an arc of layer $i$ labelled $a$.

*Item 3.* $R$ has $(n+1)|Q|$ vertices and at most $n|Q||T|$ arcs, built layer by layer with adjacency lists. The forward pass is a breadth-first search from $q_0^1$ and the backward pass a breadth-first search over reversed arcs from the accepting vertices of layer $n+1$; an arc survives iff its tail is reached forward and its head backward. By the linked BFS bound, with one added vertex joined to the accepting vertices of layer $n+1$ for the backward pass, both searches cost $O(|V(R)|+|E(R)|)$, which is $O(n|T||Q|)$ because $n,|T|,|Q|\ge1$ give $(n+1)|Q|\le 2n|T||Q|$. Van Hoeve and Katriel note that the propagator is incremental: after a deletion only the arcs with that label in that layer are removed and the two passes are repeated on the affected part of $R$.

## Sources

- W.-J. van Hoeve and I. Katriel, "Global constraints", in F. Rossi, P. van Beek and T. Walsh (eds.), *Handbook of Constraint Programming*, Elsevier (2006), chapter 6, 169–208, doi:10.1016/S1574-6526(06)80010-6; author copy [https://www.andrew.cmu.edu/user/vanhoeve/papers/chapter.pdf](https://www.andrew.cmu.edu/user/vanhoeve/papers/chapter.pdf). Definition 3, the graph $R$, Theorem 10 and Corollary 11 (attributed to Pesant), the forward/backward filtering algorithm with its $O(n|\Sigma||Q|)$ time and space bound, Figs. 7.5–7.6 and the incremental version, §7.3.3 (section and theorem numbers of the author copy).
- G. Pesant, "A regular language membership constraint for finite sequences of variables", *Principles and Practice of Constraint Programming – CP 2004*, Lecture Notes in Computer Science 3258 (2004), 482–495, doi:10.1007/978-3-540-30201-8_36. The original algorithm, credited by the handbook.
