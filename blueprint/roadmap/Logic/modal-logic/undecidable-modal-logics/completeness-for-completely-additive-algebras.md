# Completeness for completely additive algebras is undecidable

Whether a finitely axiomatized normal modal logic with at least three diamonds is complete with respect to Boolean algebras with completely additive operators is undecidable, in the spirit of Thomason's undecidability of Kripke completeness.

**Theorem (Holliday and Litak).** A *BAO* (Boolean algebra with operators) has unary operators $\lozenge_i$ preserving finite joins and $\bot$; it is a *$\mathcal V$-BAO* if every operator is *completely additive*: whenever $\bigvee X$ exists, $\lozenge_i \bigvee X = \bigvee\{\lozenge_i x \mid x \in X\}$. A normal modal logic $\mathbf L$ is *$\mathcal V$-complete* if $\mathbf L$ is the set of formulas valid on some class of $\mathcal V$-BAOs (equivalently, every formula valid on all $\mathcal V$-BAOs validating $\mathbf L$ belongs to $\mathbf L$). $\mathcal V$-completeness is undecidable for normal modal logics with at least three modal operators (Corollary 6.6 of the source): there is no algorithm that decides, given a finite set of formulas axiomatizing a normal modal logic $\mathbf L$ in a language with at least three diamonds, whether $\mathbf L$ is $\mathcal V$-complete.

The same holds for any class of normal unimodal logics containing Thomason's simulation logic $\mathrm{Sim}(3)$ (Corollary 6.7 of the source, with proof sketched). By contrast, consequence over $\mathcal V$-BAOs is recursively axiomatizable, since the class of $\mathcal V$-BAOs is first-order definable (Corollary 6.8), unlike consequence over complex algebras of Kripke frames.

## Depends on

- [Boolean algebra](../../../Order/lattices-boolean-algebras/boolean-algebra.md)

## Proof depends on

None.

## Expansion

Thomason (1982) and Kracht and Wolter (1999) proved that every property of polymodal logics that is *reflected by fusions* ($\mathbf L_1, \mathbf L_2$ have it whenever $\mathbf L_1 \otimes \mathbf L_2$ has it) and *finitely nontrivial* (the inconsistent logic in every signature has it, and some finitely axiomatizable logic lacks it) is undecidable for normal modal logics with at least three operators (Theorem 6.4 of the source); the proof rests on Thomason's theorem that consistency of the logic axiomatized by a formula with at least two modal operators is undecidable. Complete additivity is preserved by modal reducts, so $\mathcal V$-completeness is reflected by fusions (Corollary 6.5); it is finitely nontrivial: the inconsistent logic is trivially $\mathcal V$-complete, while finitely axiomatized $\mathcal V$-incomplete logics exist (Section 5 of the source, for instance via Theorem 5.2: every logic between van Benthem's logic $\mathbf{vB}$ and $\mathbf{ID}$ is $\mathcal V$-incomplete).

## Sources

- W. H. Holliday and T. Litak, "Complete additivity and modal incompleteness", *The Review of Symbolic Logic* 12(3):487–535, 2019, <https://doi.org/10.1017/S1755020317000259>; numbers from arXiv:1809.07542v2, <https://arxiv.org/abs/1809.07542v2>: Definition 3.1, Theorem 5.2, Theorem 6.4, Corollaries 6.5 to 6.8.
- S. K. Thomason, "Undecidability of the completeness problem of modal logic", in *Universal Algebra and Applications*, Banach Center Publications 9, PWN, 1982, pp. 341–345: the undecidability of consistency used in Theorem 6.4; not read directly here: this clause rests on its statement in the arXiv copy of the first source above (Theorem 6.4 and its proof).
- M. Kracht and F. Wolter, "Normal monomodal logics can simulate all others", *The Journal of Symbolic Logic* 64(1):99–138, 1999, <https://doi.org/10.2307/2586754>: the general form of Theorem 6.4 and the simulation logic; not read directly here: this clause rests on its statement in the arXiv copy of the first source above (Theorem 6.4 and Corollary 6.7).
