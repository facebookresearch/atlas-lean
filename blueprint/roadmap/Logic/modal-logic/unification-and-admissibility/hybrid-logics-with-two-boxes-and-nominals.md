# Hybrid logics with two boxes and nominals

The language $\mathcal{H}_2$ has propositional variables, nominals (atoms true at exactly one point) and two boxes $\Box$ and $\Box_h$. $\mathbf{K}_{\mathcal{H}_2}$ is the set of its formulas valid in all frames $(W, R, S)$, and $\mathbf{K}_{\mathcal{H}_2} \oplus 45$ the set valid in all frames with $R$ transitive and $S = W \times W$.

**Syntax.** $\mathcal{H}_2$-formulas are built from an infinite list $p_1, p_2, \dots$ of propositional variables and an infinite list $n_1, n_2, \dots$ of *nominals* with the Boolean connectives and two unary modal operators $\Box$ and $\Box_h$.

**Semantics.** A frame is a triple $\mathfrak{F} = (W, R, S)$ with $R, S \subseteq W \times W$. A model adds a valuation $\mathfrak{V}$ sending each variable $p_i$ to a subset of $W$ and each nominal $n_i$ to a *singleton* subset of $W$. Truth is defined by $x \models n_i$ iff $\{x\} = \mathfrak{V}(n_i)$, $x \models \Box\psi$ iff $\psi$ is true at every $y$ with $x R y$, $x \models \Box_h\psi$ iff $\psi$ is true at every $y$ with $x S y$, and the Boolean clauses are as usual. $\mathbf{K}_{\mathcal{H}_2}$ is the set of formulas valid in all frames; $\mathbf{K}_{\mathcal{H}_2} \oplus 45$ is the set valid in all frames with $R$ transitive and $S = W \times W$, so that $\Box_h$ is the universal modality there.

A *substitution* for $\mathcal{H}_2$ maps propositional variables to $\mathcal{H}_2$-formulas and leaves nominals unchanged. Satisfiability is PSPACE-complete for $\mathbf{K}_{\mathcal{H}_2}$ and EXPTIME-complete for $\mathbf{K}_{\mathcal{H}_2} \oplus 45$ (Fact 4.1 of the source, recalled from Areces, Blackburn and Marx).

## Depends on

- [Kripke model](../kripke-semantics/kripke-model.md)

## Proof depends on

None.

## Expansion

$\mathcal{H}_2$ is the two-operator fragment of the minimal hybrid language $\mathcal{H}$ with infinitely many boxes and nominals; under the standard correspondence between modal and description languages, the multimodal version is a notational variant of the description logic $\mathcal{ALCO}$.

## Sources

- F. Wolter and M. Zakharyaschev, "Undecidability of the unification and admissibility problems for modal and description logics", *ACM Transactions on Computational Logic* 9(4):1–20, 2008, doi:10.1145/1380572.1380574; read as arXiv:cs/0609052v1, <https://arxiv.org/abs/cs/0609052v1>: Section 4, the definitions of $\mathcal{H}_2$, $\mathbf{K}_{\mathcal{H}_2}$, $\mathbf{K}_{\mathcal{H}_2} \oplus 45$ and substitutions, and Fact 4.1.
