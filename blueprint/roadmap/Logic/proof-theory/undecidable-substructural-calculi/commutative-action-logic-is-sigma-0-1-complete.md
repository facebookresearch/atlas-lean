# Commutative action logic is Σ⁰₁-complete and its infinitary version is Π⁰₁-complete

The equational theory of commutative action lattices is Σ⁰₁-complete, and the equational theory of commutative *-continuous action lattices is Π⁰₁-complete, as in the non-commutative case.

**Theorem (Kuznetsov).** An *action lattice* is a structure $(A; \preceq, \cdot, 0, 1, \backslash, /, \vee, \wedge, {}^*)$ in which $(A; \preceq, \vee, \wedge)$ is a lattice with least element $0$, $(A; \cdot, 1)$ is a monoid, $\backslash$ and $/$ are the residuals of $\cdot$ with respect to $\preceq$ ($b \preceq a \backslash c \iff a \cdot b \preceq c \iff a \preceq c / b$), and $a^* = \min\{b \mid 1 \preceq b \text{ and } a \cdot b \preceq b\}$; it is *commutative* if $\cdot$ is, and $*$-continuous if $a^* = \sup\{a^n \mid n \ge 0\}$ for every $a$. *Commutative action logic* $\mathbf{CommACT}$ is the set of inequations valid in all commutative action lattices, and *infinitary commutative action logic* $\mathbf{CommACT}_\omega$ the set valid in all commutative $*$-continuous action lattices; both are presented by sequent calculi, the latter with an $\omega$-rule for the star. Then:

1. derivability in $\mathbf{CommACT}_\omega$ is $\Pi^0_1$-complete (Theorems 5 and 6 of the source);
2. derivability in $\mathbf{CommACT}$ is $\Sigma^0_1$-complete (Theorem 11).

The non-commutative counterparts, action logic and infinitary action logic, have the same degrees ([logics between action logic and infinitary action logic are undecidable](logics-between-act-and-act-omega-are-undecidable.md)), but the methods differ.

## Depends on

- [Action logic and infinitary action logic](action-logic-and-infinitary-action-logic.md)
- [The arithmetical class $\Sigma_n$](../../../TheoryOfComputation/degrees-and-hierarchies/arithmetical-hierarchy/is-sigma.md)
- [The arithmetical class $\Pi_n$](../../../TheoryOfComputation/degrees-and-hierarchies/arithmetical-hierarchy/is-pi.md)

## Proof depends on

- [Two-counter machines are universal](../../../TheoryOfComputation/equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)
- [Myhill's characterization of creative sets](../../../TheoryOfComputation/computability/halting-problem-and-rice-s-theorem/myhill-s-characterization-of-creative-sets.md)

## Expansion

*Upper bounds.* $\mathbf{CommACT}_\omega$ enjoys cut elimination, and derivability of a sequent reduces to derivability of all its $\omega$-rule premises with bounded star, which gives membership in $\Pi^0_1$ (Theorem 5); $\mathbf{CommACT}$ is recursively enumerable.

*Lower bounds.* For a Minsky machine $M$ and input $x$, a sequent $E^*, q_S, a^x \vdash D$ is built that is derivable in $\mathbf{CommACT}_\omega$ iff $M$ runs forever on $x$ (Theorem 6), giving $\Pi^0_1$-hardness. The same sequent is derivable in $\mathbf{CommACT}$ whenever $M$ runs circularly, revisiting a configuration, and only if $M$ does not halt. The sets of circularly running and of halting machines are effectively inseparable, so the set of machines whose sequent is derivable in $\mathbf{CommACT}$, which lies between them and is recursively enumerable, is creative and hence $\Sigma^0_1$-complete by Myhill's theorem (Theorems 8 to 11).

## Sources

- S. L. Kuznetsov, "Commutative action logic", *Journal of Logic and Computation* 33(6):1437–1462, 2023 (published online 2022), <https://doi.org/10.1093/logcom/exac008>; numbers from arXiv:2102.11639v1, <https://arxiv.org/abs/2102.11639v1>: Section 1 (action lattices), Theorems 2, 5, 6, 8, 9, 10 and 11.
