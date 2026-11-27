# SHN with arbitrary roles in number restrictions is undecidable

In the description logic SHN, with transitive roles, role hierarchies and unqualified number restrictions, allowing number restrictions on roles that are transitive or have transitive subroles makes concept satisfiability with respect to general axioms undecidable.

**SHN.** Roles are role names, some of which are declared transitive; a *role hierarchy* is a finite set of inclusions $R \sqsubseteq S$ between roles, and the sub-role relation is the reflexive-transitive closure of these inclusions. Concepts extend those of [ALC syntax, semantics and reasoning tasks](../alc-syntax-semantics-and-reasoning-tasks.md) by unqualified number restrictions $(\leq n\; R)$ and $(\geq n\; R)$, interpreted as the sets of elements with at most, respectively at least, $n$ $R$-successors. A role is *simple* if it is neither transitive nor has a transitive sub-role. In SHN, as in SHIQ, number restrictions may only use simple roles; *SHN⁺* lifts this restriction. An interpretation satisfies a role hierarchy if $R^{\mathcal{I}} \subseteq S^{\mathcal{I}}$ for each inclusion, and interprets transitive roles by transitive relations.

**Theorem (Horrocks, Sattler and Tobies).** Satisfiability of SHN⁺ concepts with respect to a role hierarchy and a finite set of general concept inclusions is undecidable.

Hence all standard inference problems for SHN⁺ are undecidable. With number restrictions restricted to simple roles, the logic SHIQ, which contains SHN, is decidable; the source leaves open the corresponding question for SHIF with arbitrary roles in functional restrictions.

## Depends on

- [ALC syntax, semantics and reasoning tasks](../alc-syntax-semantics-and-reasoning-tasks.md)

## Proof depends on

- [The tiling problem is undecidable](../../../TheoryOfComputation/undecidable-problems/wang-tiles/the-tiling-problem-is-undecidable.md)

## Expansion

The proof reduces the $\mathbb{N} \times \mathbb{N}$ domino problem, adapting a construction of Baader and Sattler. Two horizontal roles $X_1, X_2$ and two vertical roles $Y_1, Y_2$ alternate in the grid, disjoint concepts $A, B, C, D$ mark the four kinds of points, and for each combination of an $X$-role and a $Y$-role a transitive super-role $S^\oplus_{ij}$ connects each point exactly to its right, upper and diagonal neighbors; the number restriction $(\leq 3\; S^\oplus_{ij})$ then forces the $X \circ Y$ and $Y \circ X$ successors to coincide. Axioms for the local matching conditions complete the reduction: $A$ is satisfiable with respect to the axioms iff the domino system tiles the grid.

## Sources

- I. Horrocks, U. Sattler and S. Tobies, "Practical reasoning for very expressive description logics", *Logic Journal of the IGPL* 8(3):239–263, 2000, doi:10.1093/jigpal/8.3.239; read as arXiv:cs/0005013v1, <https://arxiv.org/abs/cs/0005013v1>, whose numbering is used here: Definition 2.1 (syntax and semantics of the S family) and Section 5 ("The undecidability of unrestricted SHN").
