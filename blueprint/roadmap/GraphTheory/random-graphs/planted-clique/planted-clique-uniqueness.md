# Uniqueness of the planted clique

Fix $\varepsilon > 0$, and for each $n$ let $S \subseteq \{1, \dots, n\}$ have size $k = |S| \ge \varepsilon\sqrt n$. Then almost surely, that is with probability tending to $1$ as $n \to \infty$, the planted set $S$ is the unique largest clique of $G(n, 1/2, S)$: every other clique has fewer than $k$ vertices.

## Proof sketch

Relabelling the vertices shows that the probability depends only on $n$ and $k$, so it is the same for a fixed $S$ as for the uniformly random $k$-set of Alon, Krivelevich and Sudakov. A quantitative bound: a fixed set $T$ disjoint from $S$ is a clique with probability exactly $2^{-\binom{|T|}{2}}$, and for every $r$ with $8r \le 3k$,

$$
\Pr\bigl[\exists\, Q \ne S \text{ a clique with } |Q| = k\bigr] \le n\,e^{-k/32} + \binom{n}{r} 2^{-\binom{r}{2}}.
$$

A clique $Q \ne S$ of size $|S|$ either contains a vertex outside $S$ adjacent to more than $\tfrac58|S|$ vertices of $S$, or contains at least $\tfrac38|S| \ge r$ vertices outside $S$ forming a clique. The first event is bounded by the outside-degree lemma and the second by a union bound over $r$-subsets disjoint from $S$. With $r = \lfloor 3k/8 \rfloor$ and $k \ge \varepsilon\sqrt n$ both terms tend to $0$, and a larger clique would contain a clique of size $k$ other than $S$.

## Depends on

- [Planted clique model, search and detection problems](planted-clique-model.md)

## Proof depends on

- [Outside vertices have at most 5|S|/8 neighbors in the planted clique](planted-clique-outside-degrees.md)

## Sources

- Noga Alon, Michael Krivelevich and Benny Sudakov, "Finding a large hidden clique in a random graph", Random Structures & Algorithms 13(3-4), 1998, Section 1 (p. 458), Section 2.2 (p. 459) and Section 3 (p. 464).
