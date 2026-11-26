# Gödel–Gentzen negative translation

This node covers the negative translation of classical into intuitionistic first-order logic.

With $\neg A$ abbreviating $A \to \bot$, the translation $g$ is defined by recursion on formulas:
$g(\bot) = \bot$; $g(P) = \neg\neg P$ for other atomic $P$; $g(A \wedge B) = g(A) \wedge g(B)$;
$g(A \vee B) = \neg(\neg g(A) \wedge \neg g(B))$; $g(A \to B) = g(A) \to g(B)$;
$g(\forall x A) = \forall x\, g(A)$; and $g(\exists x A) = \neg \forall x \neg g(A)$. The main
results: classical predicate logic proves $A \leftrightarrow g(A)$; intuitionistic predicate logic
proves $g(A) \leftrightarrow \neg\neg g(A)$; and $A$ is provable classically exactly when $g(A)$ is
provable intuitionistically. The cited survey takes $\neg$ as primitive, with the clause
$g(\neg A) = \neg g(A)$, and has no $\bot$; this page instead takes $\bot$ as primitive, defines
$\neg A$ as $A \to \bot$ and sets $g(\bot) = \bot$, so the survey's negation clause becomes an
instance of the implication clause.

## Expansion

A sound expansion fixes one definition of the translation on the chosen syntax, stating which
connectives are primitive and the clause for each (definitions with the same name differ in their
clauses, for example for atoms and disjunction), and has separate pages for: the translation; the
two equivalences; the formula-level equivalence of provability, whose converse direction uses the
classical equivalence of $A$ and $g(A)$; and the version for a set $T$ of closed sentences used as
axioms: $T$ proves $\sigma$ classically exactly when $\{g(\tau) : \tau \in T\}$ proves
$g(\sigma)$ intuitionistically. $T$ is a set of axioms, not the set of all classical truths. The
translation is not the identity up to intuitionistic equivalence.

## Sources

- J. Moschovakis, *Intuitionistic logic*, Stanford Encyclopedia of Philosophy, substantive revision 16 December 2022, §4.1. <https://plato.stanford.edu/entries/logic-intuitionistic/>
