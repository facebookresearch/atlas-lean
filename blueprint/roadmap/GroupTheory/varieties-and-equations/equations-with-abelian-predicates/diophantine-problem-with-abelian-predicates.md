# Diophantine problem with abelian predicates

The Diophantine problem with abelian predicates of a group $G$ asks whether a finite system of equations over $G$ has a solution whose image in the abelianization $G^{\mathrm{ab}}$ also satisfies a given finite system of equations there.

Let $G$ be a group with a finite generating set and let $\mathbf{x} = \{X_1, \dots, X_m\}$ be variables. A finite system of equations over $G$ is a finite subset $\{w_1, \dots, w_n\}$ of the free product $G * F(\mathbf{x})$; a solution is a homomorphism $\phi\colon G * F(\mathbf{x}) \to G$ that is the identity on $G$ and maps every $w_i$ to $1$. Let $\mathrm{ab}\colon G \to G^{\mathrm{ab}} = G / [G, G]$ be the abelianization. The Diophantine problem with abelian predicates, $\mathcal{DP}(G, \mathrm{ab})$, asks for an algorithm that decides, given

- a finite system of equations $\{w_1, \dots, w_n\}$ over $G$ (with constants written as words in the generators), and
- a finite system $\Theta$ of equations in $G^{\mathrm{ab}}$ in the unknowns $\mathrm{ab}(X_1), \dots, \mathrm{ab}(X_m)$, with constants from $G^{\mathrm{ab}}$,

whether some solution $\phi$ of the system satisfies $\Theta$ when each $\mathrm{ab}(X_i)$ is replaced by $\mathrm{ab}(\phi(X_i))$. Equivalently, it is the existential positive theory of $G$ expanded by the binary relation $\{(g, h) \in G^2 : \mathrm{ab}(g) = \mathrm{ab}(h)\}$.

## Depends on

- [Group](../../group-basics/group.md)
- [Commutator subgroup of a group](../../commutators-and-engel-conditions/commutator-subgroup.md)
- [Quotient group by a normal subgroup](../../group-basics/quotient-group.md)
- [Abelian group](../../group-basics/abelian-group.md)
- [Abelianization of a group](../../commutators-and-engel-conditions/abelianization.md)
- [Solution set of a system of equations](../equationally-noetherian-groups/solutions-2.md)

## Proof depends on

None.

## Expansion

Without the constraints this is the Diophantine problem of $G$, decidable for free groups (Makanin), right-angled Artin groups and hyperbolic groups. The abelian predicate is the group analogue of the "abelian equivalence" length constraints studied for word equations in free monoids, where Büchi and Senger showed undecidability. For groups with finite abelianization the constraints reduce to recognizable constraints, and the source proves the problem decidable there for hyperbolic groups and graph products of finite groups.

## Sources

- L. Ciobanu and A. Garreta, "Group equations with abelian predicates", International Mathematics Research Notices 2024 (2024), no. 5, 4119–4159, https://doi.org/10.1093/imrn/rnad179; read in arXiv:2204.13946v1 (Sections 2.1 and 2.2 of arXiv:2204.13946v1, the Diophantine problem in groups and with constraints).
