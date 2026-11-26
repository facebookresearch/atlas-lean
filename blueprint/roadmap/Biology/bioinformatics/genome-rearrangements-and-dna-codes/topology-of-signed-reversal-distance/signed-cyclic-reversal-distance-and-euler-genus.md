# Signed cyclic reversal distance and Euler genus

**Setting.** A *signed cyclic permutation* (sc-permutation) $\pi$ of $\{1,\dots,n\}$ is a cyclic arrangement of the elements, each carrying a sign; it models a circular single-chromosome genome with gene orientations. An *sc-reversal* reverses the order and flips the signs of a cyclic interval. The sc-reversal distance $d^c(\pi,I)$ is the least number of sc-reversals turning $\pi$ (or its flip) into the identity $I=(1,\dots,n)$ (or its flip).

Identify $\pi$ with a two-vertex embedding scheme: $n$ edges joining two vertices, rotation $I$ at one vertex, the mirror of $\pi$ at the other, and edge signatures given by the signs. Let $e(\pi)=n$ be its number of edges, $f(\pi)$ its number of faces, and $eg(\pi)=e(\pi)-f(\pi)$ its Euler genus. Call $i,i+1$ a *reversible pair* if they have opposite signs, and $\pi$ *non-orientable* if it has elements of both signs.

**Theorem (Bafna–Pevzner bound from Euler's formula).** For every sc-permutation,

$$d^c(\pi,I)\ \ge\ e(\pi)-f(\pi)=eg(\pi).$$

**Lemma (progress).** If $(i,i+1)$ is a reversible pair and $\sigma$ is an sc-reversal making $i$ and $i+1$ homotopic (adjacent and consistently oriented), then $eg(\pi\cdot\sigma)=eg(\pi)-1$.

**Theorem (exactness for reduced non-orientable permutations).** If $\pi$ is non-orientable and reduced (its embedding scheme has a single portion, i.e. no proper sub-block that a reversal sequence must treat separately), then

$$d^c(\pi,I)=eg(\pi),$$

and a Hannenhalli–Pevzner type algorithm, repeatedly reversing a reversible pair of highest score in the interleaving graph, produces an optimal sorting sequence. Without these hypotheses the inequality can be strict, for instance for the embedding schemes of Theorem 1.3 of the source (exactly one non-trivial positive block and one non-trivial negative block) and for the example of its Figure 3.

## Expansion

A sorting sequence of length $d$ draws the two-vertex scheme on a cylinder: each element traces an $x$-monotone arc between the two vertices, and each reversal is realized by gluing one cross-cap where the reversed arcs cross. This yields a drawing with $d$ cross-caps, i.e. an embedding in a non-orientable surface of Euler genus at most $d$, so $d\ge eg(\pi)$ by Euler's formula $2-eg=2-e+f$. Reversing a reversible pair into homotopic position merges two faces' worth of boundary, lowering $eg$ by exactly one; the remaining difficulty is to avoid creating orientable components in the interleaving graph, which the highest-score rule guarantees, so in the reduced non-orientable case every step makes progress. The same correspondence shows that Mohar's conjecture (degenerate crossing number equals non-orientable genus) is a statement about such perfect cross-cap drawings.

## Sources

- Niloufar Fuladi, Alfredo Hubard, Arnaud de Mesmay, "Degenerate crossing number and signed reversal distance", arXiv:2308.10666: Section 2.4 (sc-reversals and cross-cap drawings), Section 4.1 (Bafna–Pevzner inequality from Euler's formula, its strictness for the schemes of Theorem 1.3 and Figure 3, and the progress Lemma 4.1), Theorem 4.2 and Lemma 4.3 (exactness for reduced non-orientable sc-permutations), Section 4.3 (interleaving graph), Section 3, Theorem 1.3 and Corollary 1.4 (schemes without perfect cross-cap drawings). <https://doi.org/10.48550/arXiv.2308.10666> Published version: Graph Drawing and Network Visualization (GD 2023), Lecture Notes in Computer Science 14465 (2023) 95–109, <https://doi.org/10.1007/978-3-031-49272-3_7>.
