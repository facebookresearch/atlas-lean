# Uniqueness of the planted clique

In $G(n, 1/2, S)$ with $|S| \ge 1$: a fixed set $T$ disjoint from $S$ is a clique with probability exactly $2^{-\binom{|T|}{2}}$, and for every $r$ with $8r \le 3|S|$,

$$
\Pr\bigl[\exists\, Q \ne S \text{ a clique with } |Q| = |S|\bigr] \le n\,e^{-|S|/32} + \binom{n}{r} 2^{-\binom{r}{2}}.
$$

## Proof sketch

A clique $Q \ne S$ of size $|S|$ either contains a vertex outside $S$ adjacent to more than $\tfrac58|S|$ vertices of $S$, or contains at least $\tfrac38|S| \ge r$ vertices outside $S$ forming a clique. The first event is bounded by the outside-degree lemma and the second by a union bound over $r$-subsets disjoint from $S$.

## Depends on

- [Planted clique model, search and detection problems](planted-clique-model.md)

## Proof depends on

- [Outside vertices have at most 5|S|/8 neighbors in the planted clique](planted-clique-outside-degrees.md)

## Sources

- Noga Alon, Michael Krivelevich and Benny Sudakov, "Finding a large hidden clique in a random graph", Random Structures & Algorithms 13(3-4), 1998.
