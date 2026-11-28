# Atomic μ-calculus

The atomic μ-calculus extends the modal μ-calculus by disjunctions over orbit-finite sets of formulas, built from basic propositions that may mention atoms, and is interpreted over atomic Kripke models.

**Definition.** Over atoms $\mathbb A$ as in [atomic Kripke models](atomic-kripke-models.md), fix an equivariant set $P$ of basic propositions and an equivariant set of variables. Formulas of the (scalar) *atomic μ-calculus* are

$$
\varphi ::= p \mid X \mid \textstyle\bigvee\Phi \mid \neg\varphi \mid \lozenge\varphi \mid \mu X.\varphi,
$$

where $\Phi$ ranges over orbit-finite sets of formulas and $X$ occurs only positively in $\mu X.\varphi$; $\bigwedge\Phi$, $\square$ and $\nu$ are defined as usual. In an atomic Kripke model and a variable environment, formulas are evaluated as in the classical case, an orbit-finite disjunction holding at a state iff some disjunct does.

## Depends on

- [Atomic Kripke models](atomic-kripke-models.md)
- [Formulas of the modal μ-calculus](../../modal-logic/modal-calculus/mu-formula.md)

## Proof depends on

None.

## Remarks

Orbit-finite disjunctions act as quantifiers over atoms: with $P = \mathbb A$, the formula $\bigvee_{a \in \mathbb A}\lozenge(a \wedge \bigwedge_{b \neq a}\neg b)$ is a legal formula. Every formula has finite depth and is finitely supported, and the semantics of a formula in a finitely supported model, under a finitely supported environment for its free variables, is a finitely supported set of states (Lemma 4.9 of the source).

## Sources

- B. Klin and M. Łełyk, "Scalar and Vectorial mu-calculus with Atoms", *Logical Methods in Computer Science* 15(4), 2019, paper 5, <https://doi.org/10.23638/LMCS-15(4:5)2019>; numbers from arXiv:1803.06752v3, <https://arxiv.org/abs/1803.06752v3>: Section 2 (Definitions 2.1 to 2.3) and Section 4 (Definition 4.1, Example 4.2 and Definition 4.7).
