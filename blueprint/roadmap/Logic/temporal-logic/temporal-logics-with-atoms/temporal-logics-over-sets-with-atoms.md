# Temporal logics over sets with atoms

The atomic μ-calculus, atomic CTL* and atomic LTL extend their classical counterparts by disjunctions and conjunctions over orbit-finite sets of formulas, built from basic propositions that may mention atoms, and are interpreted over Kripke models that are finitely supported sets with atoms.

**Definition.** Fix a countably infinite set $\mathbb A$ of *atoms*, either with equality only (*equality atoms*) or with a dense linear order (*ordered atoms*), and let $\mathrm{Aut}(\mathbb A)$ be its automorphism group, acting on the von Neumann-like universe of sets built from atoms. A finite $S \subseteq \mathbb A$ *supports* a set $x$ if every automorphism fixing $S$ pointwise fixes $x$; $x$ is *equivariant* if $\emptyset$ supports it. A finitely supported set is *orbit-finite* if it is a finite union of orbits under the automorphisms fixing some support. For example $\mathbb A$ and $\mathbb A^n$ are equivariant and orbit-finite, while $\mathbb A^*$ is not orbit-finite.

*Atomic μ-calculus.* For an equivariant set $P$ of basic propositions and an equivariant set of variables, formulas are

$$
\varphi ::= p \mid X \mid \textstyle\bigvee\Phi \mid \neg\varphi \mid \lozenge\varphi \mid \mu X.\varphi,
$$

where $\Phi$ ranges over orbit-finite sets of formulas and $X$ occurs only positively in $\mu X.\varphi$; $\bigwedge\Phi$, $\square$ and $\nu$ are defined as usual. *Atomic CTL** and *atomic LTL* are defined in the same way from CTL* (state formulas $\Phi ::= p \mid \Phi \vee \Phi \mid \neg\Phi \mid \exists\varphi$, path formulas $\varphi ::= \Phi \mid \varphi \vee \varphi \mid \neg\varphi \mid \varphi\,\mathbf U\,\varphi \mid \mathbf X\varphi$) and from LTL, its fragment without $\exists$, adding orbit-finite disjunctions.

*Models.* An *atomic Kripke model* $\mathcal K = \langle K, \to, \models\rangle$ consists of a set with atoms $K$, a finitely supported transition relation $\to \subseteq K \times K$ and a finitely supported relation $\models \subseteq K \times P$ for basic propositions; it is *orbit-finite* if $K$ is. Formulas are evaluated as in the classical case, an orbit-finite disjunction holding at a state iff some disjunct does. Atomic LTL formulas are interpreted over deterministic models, in which every state has exactly one successor, so each state determines an infinite path.

## Depends on

- [Kripke model](../../modal-logic/kripke-semantics/kripke-model.md)
- [Formulas of the modal μ-calculus](../../modal-logic/modal-calculus/mu-formula.md)
- [Formulas of linear temporal logic](../linear-temporal-logic/formula.md)
- [State formulas of CTL$^{\ast}$](../ctl/ctl-state-and-path-formulas/state-formula.md)

## Proof depends on

None.

## Expansion

Orbit-finite disjunctions act as quantifiers over atoms: with $P = \mathbb A$, the formula $\bigvee_{a \in \mathbb A}\lozenge(a \wedge \bigwedge_{b \neq a}\neg b)$ is a legal formula. Every formula has finite depth and is finitely supported, and the semantics of a formula in a finitely supported model is a finitely supported set of states. For CTL* one may let path quantifiers range over all paths or over finitely supported ones only; the undecidability of model checking holds either way.

## Sources

- B. Klin and M. Łełyk, "Scalar and Vectorial mu-calculus with Atoms", *Logical Methods in Computer Science* 15(4), 2019, paper 5, <https://doi.org/10.23638/LMCS-15(4:5)2019>; numbers from arXiv:1803.06752v3, <https://arxiv.org/abs/1803.06752v3>: Section 2 (Definitions 2.1 to 2.5), Section 3 (sets with atoms, equality and ordered atoms, Example 3.3) and Section 4 (Definition 4.1, Example 4.2, Definition 4.4, Definition 4.7 and the paragraph introducing atomic CTL* and LTL).
