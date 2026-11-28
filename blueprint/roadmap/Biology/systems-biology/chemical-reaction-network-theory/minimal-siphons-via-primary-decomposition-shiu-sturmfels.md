# Relevant minimal siphons via primary decomposition of saturations

For a chemical reaction network $G$ with complexes $y_1, \dots, y_n$ on species $1, \dots, s$ and concentration variables $c_1, \dots, c_s$, Shiu and Sturmfels (2010) define the ideals $T_G = \langle c^{y_i}(c^{y_j} - c^{y_i}) : y_i \to y_j \text{ a reaction}\rangle$, $J_G = \langle c^{y_j} - c^{y_i} : y_i \to y_j \text{ a reaction}\rangle$ and the monomial ideal $M_G = \langle c^{y_1}, \dots, c^{y_n}\rangle$, all taken in the quotient ring $R = \mathbb{Q}[c_1, \dots, c_s]/\langle c_1 c_2 \cdots c_s\rangle$. Their Theorem 3.1, which reads the minimal nonempty [siphons](persistence-of-mass-action-systems/siphon-criterion-for-persistence-angeli-de-leenheer-sontag.md) of $G$ off the minimal primes of $T_G$ (written $I_G$ there), of $J_G$, and of $M_G$, is stated as [minimal siphons from the binomial ideal `I_G`](../../not-yet-classified/siphon-prime-decomposition/is-minimal-siphon-iff-ideal-i.md), [minimal siphons from `J_G`](../../not-yet-classified/siphon-prime-decomposition/is-minimal-siphon-iff-ideal-j.md) and [minimal siphons from the monomial ideal `M_G`](../../not-yet-classified/siphon-prime-decomposition/is-minimal-siphon-iff-ideal-m.md). Theorem 3.2 of the source describes the relevant, $c^{(0)}$-relevant and $\Omega$-relevant minimal siphons in the same way, as the inclusion-minimal sets $\{i \in [s] : c_i \in P\}$ for $P$ running over the minimal primes in $R$ of the saturations, by ideals that encode the boundary of the cone of conservation relations, of $T_G$ for every network $G$, of $J_G$ when each connected component of $G$ is strongly connected, and of $M_G$ when $G$ is strongly connected (the three rows of the theorem, with the hypotheses the source states after its display (4)).

## Depends on

- [Siphon criterion for persistence of reaction networks](persistence-of-mass-action-systems/siphon-criterion-for-persistence-angeli-de-leenheer-sontag.md)
- [Ideal I](../../not-yet-classified/siphon-prime-decomposition/ideal-i.md)
- [Ideal J](../../not-yet-classified/siphon-prime-decomposition/ideal-j.md)
- [Ideal M](../../not-yet-classified/siphon-prime-decomposition/ideal-m.md)
- [Is Minimal Siphon](../../not-yet-classified/siphon-prime-decomposition/is-minimal-siphon.md)

## Proof depends on

- [Minimal siphons from the binomial ideal `I_G`](../../not-yet-classified/siphon-prime-decomposition/is-minimal-siphon-iff-ideal-i.md)
- [Minimal siphons from `J_G`](../../not-yet-classified/siphon-prime-decomposition/is-minimal-siphon-iff-ideal-j.md)
- [Minimal siphons from the monomial ideal `M_G`](../../not-yet-classified/siphon-prime-decomposition/is-minimal-siphon-iff-ideal-m.md)

## Expansion

1. Definitions: relevant, $c^{(0)}$-relevant and $\Omega$-relevant siphons, and the saturation ideals of the source.
2. Theorem 3.2: the nine saturation ideals and the three notions of relevance, with the row hypotheses (every network for $T_G$, each connected component strongly connected for $J_G$, $G$ strongly connected for $M_G$).
3. The consequence for persistence via the [siphon criterion for persistence of reaction networks](persistence-of-mass-action-systems/siphon-criterion-for-persistence-angeli-de-leenheer-sontag.md), and the algorithm of the source.

## Sources

- A. Shiu and B. Sturmfels, Siphons in chemical reaction networks, Bull. Math. Biol. 72 (2010), 1448–1463, Theorem 3.2. <https://arxiv.org/abs/0904.4529>
