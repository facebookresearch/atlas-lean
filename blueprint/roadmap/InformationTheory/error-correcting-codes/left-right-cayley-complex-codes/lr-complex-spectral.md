# Spectral expansion of the two Cayley graphs implies square-complex expansion

Let $X = \mathrm{Cay}^2(A, G, B)$ with $|A| = |B| = \Delta$ and suppose the Cayley graphs $\mathrm{Cay}(G, A)$ and $\mathrm{Cay}(G, B)$ are both $\lambda$-spectral expanders, i.e. all nontrivial eigenvalues of their adjacency matrices have absolute value at most $\lambda$. For $a \in A$ call two $A$-edges with label $\{a, a^{-1}\}$ parallel when they are opposite sides of a square; crossing the square $\{g, ag, gb, agb\}$ sends $\{g, ag\}$ to $\{gb, agb\}$. The graph of parallel edges with label $\{a, a^{-1}\}$ is $\Delta$-regular and isomorphic to $\mathrm{Cay}(G, B)$, or to its quotient by left multiplication by $a$ when $a^2 = 1$, so every eigenvalue of its random-walk operator $M^{\parallel}_{\{a, a^{-1}\}}$ other than $1$ is at most $\lambda/\Delta$; symmetrically for $B$-edges and $\mathrm{Cay}(G, A)$.

Consequently the parallel walk mixes on squares. Let $X^{\sigma}(1)$ be the set of edges with label $\sigma$, let $M^{\parallel}$ act on functions $f : X(1) \to \mathbb{R}$ as $M^{\parallel}_\sigma$ on each $X^{\sigma}(1)$ (move from an edge, through a uniformly random square containing it, to the opposite edge), and let

$$
\langle f, f' \rangle = \tfrac12\, \mathbb{E}_{e \in X^A(1)}\bigl[f(e) f'(e)\bigr] + \tfrac12\, \mathbb{E}_{e \in X^B(1)}\bigl[f(e) f'(e)\bigr],
$$

with uniform $e$ over the $A$-edges and over the $B$-edges. If $R \subseteq X(1)$ is non-empty and $f = \mathbf{1}_R$ satisfies $\langle f, M^{\parallel} f \rangle \ge c\, \langle f, f \rangle$, then some label $\sigma$ has

$$
|R \cap X^{\sigma}(1)| \ge \Bigl(c - \frac{\lambda}{\Delta}\Bigr) \frac{|G|}{2}.
$$

## Proof sketch

Identify the edge $\{g, ag\}$ with $g$; it is the only presentation with this $a$ unless $a^2 = 1$, in which case $g$ and $ag$ give the same edge. Crossing a square is then right multiplication by a uniform $b \in B$, which commutes with left multiplication by $a$, so the parallel walk is the random walk on $\mathrm{Cay}(G, B)$, or on its quotient by $g \mapsto ag$; functions on the quotient lift to functions on $G$ invariant under $g \mapsto ag$, so its spectrum is contained in that of $\mathrm{Cay}(G, B)$. For the mixing statement write $p_\sigma = |R \cap X^{\sigma}(1)| / |X^{\sigma}(1)|$; on each label class the expander-mixing estimate gives $\langle f, M^{\parallel}_\sigma f \rangle_\sigma \le p_\sigma^2 + (\lambda/\Delta) p_\sigma$. Averaging over labels, $c\, \mathbb{E}_\sigma p_\sigma \le (\max_\sigma p_\sigma + \lambda/\Delta)\, \mathbb{E}_\sigma p_\sigma$, and $|X^{\sigma}(1)| \ge |G|/2$.

## Depends on

- [Left-right Cayley complexes](left-right-cayley-complex.md)

## Proof depends on

- [Expander mixing lemma](../../../GraphTheory/graph-families-and-operations/expander-graphs/expander-mixing-lemma.md)

## Sources

- I. Dinur, S. Evra, R. Livne, A. Lubotzky, S. Mozes, "Locally testable codes with constant rate, distance, and locality", STOC (2022), arXiv:2111.04808.
- O. Goldreich, "On the locally testable code of Dinur et al. (2021)", ECCC TR21-175 (2021).
