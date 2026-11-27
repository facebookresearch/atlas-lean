# Model checking atomic CTL* is undecidable

Model checking CTL* with orbit-finite disjunctions over atoms is undecidable, even on a fixed kind of orbit-finite, equivariant Kripke model, in contrast with the decidable model checking of the vectorial atomic μ-calculus.

**Theorem (Klin and Łełyk).** The model checking problem for [atomic CTL*](temporal-logics-over-sets-with-atoms.md) is undecidable: there is no algorithm that decides, given an orbit-finite atomic Kripke model $\mathcal K$, a state $x$ and an atomic CTL* state formula $\Phi$, whether $\mathcal K, x \models \Phi$. This holds for equality atoms and for ordered atoms, and whether path quantifiers range over all paths or over finitely supported paths only.

Since model checking the vectorial atomic μ-calculus over orbit-finite models is decidable (Theorem 5.1 of the source), atomic CTL* is not a fragment of the atomic μ-calculus, unlike in the classical setting.

## Depends on

- [Temporal logics over sets with atoms](temporal-logics-over-sets-with-atoms.md)

## Proof depends on

- [Satisfiability of atomic LTL is undecidable](satisfiability-of-atomic-ltl-is-undecidable.md)

## Expansion

For the atomic LTL formula $\varphi$ built from a Turing machine $M$ with states $Q$ and tape alphabet $\Gamma$ in the satisfiability proof, take the orbit-finite equivariant model with states $(\mathbb A \times \Gamma \times (Q \cup \{\mathit{nohead}\})) \cup \{\#\}$, the obvious basic predicates, and transitions in both directions between every two states. Every candidate word model is a path of this model starting at $\#$, so $\exists\varphi$ holds at $\#$ iff $\varphi$ is satisfiable. Since $\varphi$ forces its models to be finitely supported, the choice of path semantics does not matter.

## Sources

- B. Klin and M. Łełyk, "Scalar and Vectorial mu-calculus with Atoms", *Logical Methods in Computer Science* 15(4), 2019, paper 5, <https://doi.org/10.23638/LMCS-15(4:5)2019>; numbers from arXiv:1803.06752v3, <https://arxiv.org/abs/1803.06752v3>: Section 9: Theorem 9.3 and its proof; Theorem 5.1.
