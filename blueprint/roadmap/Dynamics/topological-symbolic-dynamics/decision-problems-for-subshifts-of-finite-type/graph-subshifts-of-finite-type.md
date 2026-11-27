# Graph subshifts of finite type

A graph subshift of finite type is a set of labeled, port-numbered, pointed graphs defined by finitely many forbidden local patterns, so that the shape of the graph is itself subject to local constraints; it extends both subshifts of finite type on groups and finitely presented groups.

**Graphs.** Fix a finite set $\pi$ of *ports* and a finite set $\Sigma$ of *labels*. A graph has a countable set of vertices, each labeled by an element of $\Sigma$; an edge joins two vertices through one port of each (or is a self-loop at one port), and each port of a vertex is used by at most one edge, so degrees are bounded by $|\pi|$. Graphs are *pointed* by a distinguished vertex, the origin, and taken modulo isomorphisms preserving the origin. With $\Pi = \pi^2$, a vertex is designated by a word $u \in \Pi^*$ giving a path of port pairs from the origin, and $\mathcal{L}(X) \subseteq \Pi^*$ is the set of paths of the graph $X$; $X_u$ is $X$ re-pointed at the end of the path $u$. The set of these graphs is $\mathcal{X}_{\Sigma, \pi}$; the *support* of a graph is the graph with its labels forgotten.

**Subshifts.** For a prefix-closed language $L \subseteq \Pi^*$, the *$L$-cut* $X|_L$ of $X$ is the subgraph induced by the vertices reached by paths of $L \cap \mathcal{L}(X)$. Given a set $\mathcal{F}$ of pairs $(F, L)$, with $F$ a finite graph and $L$ a finite prefix-closed language, the *subshift forbidding $\mathcal{F}$* is

$$
\mathcal{Z} = \{ X \in \mathcal{X}_{\Sigma, \pi} : (X_v)|_L \ne F \text{ for every } v \in \mathcal{L}(X) \text{ and every } (F, L) \in \mathcal{F} \},
$$

and it is a *graph subshift of finite type* (graph SFT) if $\mathcal{F}$ can be chosen finite. It may contain finite as well as infinite graphs.

**Cayley SFTs.** For a finitely presented group $\Gamma = \langle J \mid \mathcal{R} \rangle$, take $\pi = J \sqcup J^{-1}$ and forbid: edges not joining a port to its inverse port, vertices missing a port, and, for each relator $u \in \mathcal{R}$, every pattern on the prefixes of $u$ in which the path $u$ is not a cycle back to the origin. The resulting graph SFT $\mathcal{Z}^\Gamma_\Sigma$ contains the Cayley graph of $\Gamma$ and those of its quotients. A graph SFT is defined by *$\Gamma$-NN constraints* if its forbidden patterns are those of $\mathcal{Z}^\Gamma_\Sigma$ together with further nearest-neighbor constraints (patterns supported on one edge); for $\Gamma = \mathbb{Z}^2 = \langle a, b \mid aba^{-1}b^{-1} \rangle$ these graphs include the infinite grid, cylinders and tori.

**Periodicity.** A *path-period* of $X$ is a path $u$ with $X_u = X$; the corresponding vertices form the *stabilizer* of $X$. The graph $X$ is *strongly nonperiodic* if its stabilizer is trivial, and *strongly periodic* if its stabilizer is dense, equivalently if $X$ has only finitely many distinct re-pointings $X_u$.

## Depends on

- [Subshifts of finite type on a finitely generated group and the domino problem](subshifts-of-finite-type-on-groups.md)

## Proof depends on

None.

## Expansion

Classical subshifts of finite type on the Cayley graph of a group $\Gamma$ are recovered by fixing the support to be that Cayley graph; a graph SFT defined by $\Gamma$-NN constraints contains the corresponding classical SFT on the Cayley graph of $\Gamma$ but also configurations on quotient graphs. The source shows that a graph SFT contains a finite graph if and only if it contains a strongly periodic graph with residually finite stabilizer (Theorem 1). The finitely presented group $\Gamma$ itself is recovered from the monochromatic Cayley SFT: a word represents a cycle at the origin in every graph of $\mathcal{Z}^\Gamma_{\{0\}}$ exactly when it represents the identity of $\Gamma$.

## Sources

- P. Arrighi, A. Durbec and P. Guillon, "Graph subshifts", in: Unity of Logic and Computation (CiE 2023), Lecture Notes in Computer Science 13967, Springer, 2023, 261–274, https://doi.org/10.1007/978-3-031-36978-0_21; read in arXiv:2302.07249v3 (Sections 2 to 5, Definitions 1, 2, 4, 5 and 9, and Theorem 1 of arXiv:2302.07249v3, which numbers each kind of statement separately).
