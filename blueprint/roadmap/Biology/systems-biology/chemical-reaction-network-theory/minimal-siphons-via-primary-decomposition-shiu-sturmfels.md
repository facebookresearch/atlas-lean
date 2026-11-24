# Minimal siphons via primary decomposition

For a chemical reaction network $G$ with complexes $y_1, \dots, y_n$ on species $1, \dots, s$ and concentration variables $c_1, \dots, c_s$, Shiu and Sturmfels (2010) define the ideals $T_G = \langle c^{y_i}(c^{y_j} - c^{y_i}) : y_i \to y_j \text{ a reaction}\rangle$, $J_G = \langle c^{y_j} - c^{y_i} : y_i \to y_j \text{ a reaction}\rangle$ and the monomial ideal $M_G = \langle c^{y_1}, \dots, c^{y_n}\rangle$. Theorem 3.1 states that the minimal [siphons](../../../Biology/systems-biology/chemical-reaction-network-theory/siphon-criterion-for-persistence-angeli-de-leenheer-sontag.md) of $G$ are the inclusion-minimal sets $\{i \in [s] : c_i \in P\}$ as $P$ runs over the minimal primes of $T_G$; if each connected component of $G$ is strongly connected, $T_G$ can be replaced by $J_G$, and if $G$ is strongly connected, by $M_G$. Theorem 3.2 describes the relevant, $c^{(0)}$-relevant and $\Omega$-relevant minimal siphons in the same way, using the minimal primes of the saturations of $T_G$, $J_G$ and $M_G$ by ideals that encode the boundary of the cone of conservation relations.

## Expansion

1. Definitions: siphons (Proposition 2.1 of the source), relevant siphons, and the ideals $T_G$, $J_G$, $M_G$.
2. Theorem 3.1: the correspondence between minimal primes and minimal siphons, and the strongly connected simplifications through equality of radicals.
3. Theorem 3.2: the nine saturation ideals and the three notions of relevance.
4. The consequence for persistence via the [siphon criterion for persistence of reaction networks](../../../Biology/systems-biology/chemical-reaction-network-theory/siphon-criterion-for-persistence-angeli-de-leenheer-sontag.md), and the algorithm of the source.

## Sources

- A. Shiu and B. Sturmfels, Siphons in chemical reaction networks, Bull. Math. Biol. 72 (2010), 1448–1463, Theorems 3.1 and 3.2. <https://arxiv.org/abs/0904.4529>
