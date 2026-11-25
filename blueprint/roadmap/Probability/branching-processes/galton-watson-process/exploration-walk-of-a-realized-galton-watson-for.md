# Exploration walk of a Galton–Watson forest

Let $\nu$ be a probability law on $\mathbb N=\{0,1,2,\ldots\}$ and $k\ge1$. The labelled Galton–Watson forest with $k$ ancestors is the union of $k$ independent [labelled Galton–Watson trees](ulam-harris-labelled-galton-watson-trees-and-pro.md) with offspring law $\nu$, the $r$-th tree having its vertices labelled by words beginning with the letter $r\in\{1,\ldots,k\}$; equivalently, it is built from one independent array $(\xi_u)$ of $\nu$-distributed offspring numbers indexed by all finite words. Explore the forest in breadth-first order: generation by generation, and within a generation in lexicographic order of the labels. Let $u_1,u_2,\ldots$ be the explored vertices, let $\tau\in\{1,2,\ldots\}\cup\{\infty\}$ be the total number of vertices of the forest, and set $X_i=\xi_{u_i}$ for $i\le\tau$. For $i>\tau$ let $X_i$ be taken from an independent sequence of $\nu$-distributed variables, independent of the forest. Then:

1. $X_1,X_2,\ldots$ are independent with common law $\nu$.
2. With $S_0=k$ and $S_n=k+\sum_{i=1}^n(X_i-1)$, the total progeny is the first hitting time of zero,

    $$\tau=\inf\{n\ge1:\ S_n=0\},\qquad\inf\varnothing=\infty .$$

For $n<\tau$, $S_n$ is the number of vertices discovered but not yet explored after $n$ explorations. Special cases: for $k=1$ and $\nu=\delta_0$ the total progeny is $1$; for $k=1$ and $\nu=\delta_1$ one has $S_n=1$ for all $n$ and the total progeny is infinite.

## Depends on

- [Labelled Galton–Watson trees and projection to generation counts](ulam-harris-labelled-galton-watson-trees-and-pro.md)

## Proof depends on

- [Markov property](../../markov-chains/markov-and-strong-markov-properties/markov-property-full.md)

## Expansion

A full proof page must establish the following.

- The breadth-first order is well defined on the forest (each generation is finite), and $u_i$ is a stopping time of the exploration in the sense that the event $\{u_i=w\}$ depends only on offspring variables of words explored before step $i$.
- Item 1: conditionally on the first $i-1$ explored offspring numbers and on $\{i\le\tau\}$, the next explored word is determined and its offspring variable has not been inspected, so it is $\nu$-distributed and independent of the past; on $\{i>\tau\}$ the fresh sequence supplies the variable. This is a strong-Markov-type argument for the iid array along a sequence of random indices.
- Item 2: by induction, $S_n$ counts discovered unexplored vertices for $n<\tau$, the forest is exhausted exactly when this count first reaches zero, and $S_n\ge1$ for $n<\tau$ because each step decreases $S$ by at most one.
- The two special cases.

## Sources

- K. B. Athreya and P. E. Ney, *Branching Processes*, Springer (1972), <https://link.springer.com/chapter/10.1007/978-3-642-65371-1_1>, total progeny via a random walk (statement and proof).
