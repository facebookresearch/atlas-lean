# Quantified intuitionistic logic $\mathbf{QInt}$

$\mathbf{QInt}$ is the set of first-order formulas, over $\bot, \top, \wedge, \vee, \to, \exists, \forall$, that are true in every intuitionistic Kripke model: a partial order of worlds with expanding domains and monotone interpretations of the predicate letters.

**Language.** Countably many individual variables, countably many predicate letters of every arity, the constants $\bot$ and $\top$, the connectives $\wedge$, $\vee$, $\to$ and the quantifiers $\exists$, $\forall$; no constants, function symbols or equality. A formula is *positive* when it does not contain $\bot$.

**Semantics.** $\mathbf{QInt}$ is the set of formulas $\varphi$ of this language with $\Vdash \varphi$ in the sense of [Kripke models for intuitionistic first-order logic](../kripke-models-for-iqc.md), taking $\top$ to be forced everywhere: partial orders of worlds with nonempty expanding domains and monotone interpretations of the predicate letters, and the usual forcing clauses. For relational languages this is the set of theorems of intuitionistic predicate logic, by Kripke soundness and completeness.

## Depends on

- [Kripke models for intuitionistic first-order logic](../kripke-models-for-iqc.md)

## Proof depends on

None.

## Expansion

The *positive fragment* of a logic is its set of positive members. All logics between $\mathbf{QInt}$ and $\mathbf{QKC}$, the logic of the weak law of excluded middle, have the same positive fragment, which is why results about the positive fragment transfer along that interval.

## Sources

- M. Rybakov and D. Shkatov, "Undecidability of first-order modal and intuitionistic logics with two variables and one monadic predicate letter", *Studia Logica* 107(4):695–717, 2019, doi:10.1007/s11225-018-9815-7; read as arXiv:1706.05060v5, <https://arxiv.org/abs/1706.05060v5>: Section 3.1 (syntax and Kripke semantics of $\mathbf{QInt}$, and the definition of $\mathbf{QKC}$).
