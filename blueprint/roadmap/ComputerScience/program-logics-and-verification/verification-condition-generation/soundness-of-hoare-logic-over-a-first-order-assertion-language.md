# Soundness of Hoare logic over a first-order assertion language

Let $\mathcal{L}$ be a first-order assertion language with an interpretation $\mathcal{I}$, over any nonempty domain, and consider while programs whose expressions are terms and quantifier-free formulas of $\mathcal{L}$. [First-order arithmetic with its standard interpretation in the integers](../hoare-logic/first-order-arithmetic-as-an-assertion-language.md) is one example; the theorem is not restricted to it. Take the usual partial-correctness Hoare logic: the axiom $Q^e_x\{x := e\}Q$ (capture-avoiding substitution of $e$ for the free occurrences of $x$), the rules for sequencing, conditionals and $\mathbf{while}$ with an invariant, and the rule of consequence, whose implications are proved in a proof system $\mathcal{T}$ for $\mathcal{L}$.

**Theorem.** Each axiom is true in every interpretation, and each rule yields a formula true in every interpretation in which its premises are true. Consequently, if $\mathcal{T}$ is sound relative to $\mathcal{I}$ (the universal closure of every formula provable in $\mathcal{T}$ is true in $\mathcal{I}$) and $P\{A\}Q$ is derivable, then every terminating execution of $A$ from a state satisfying $P$ ends in a state satisfying $Q$.

## Expansion

The assignment case of the proof uses the substitution property of first-order satisfaction: $Q^e_x$ holds in a state exactly when $Q$ holds in the state updated at $x$ with the value of $e$. Before this page becomes ready, add a page for that property (or link one), sourced from a logic text that proves it, and list it under Proof depends on.

## Depends on

No separate prerequisite pages: the assertion language, its interpretation, the while programs and the axiom and rules are given above. The arithmetic page linked above is an example, not a hypothesis.

## Proof depends on

The substitution property listed in Expansion is needed for assignment. The remaining cases use structural induction on derivations.

## Sources

- S. A. Cook, "Soundness and completeness of an axiom system for program verification", *SIAM Journal on Computing* 7(1):70–90, 1978, <http://www.cs.utoronto.ca/~sacook/homepage/soundness.pdf>: Section 2 (the language, with the arithmetic language as the concrete example), Section 3 (substitution notation and the interpretive model for an arbitrary interpretation with a nonempty domain), Section 4 (axioms and rules), Section 5, Theorem 1 and its Corollary. Cook's language also has blocks and non-recursive procedures with their rules; this page states the while-program fragment.
