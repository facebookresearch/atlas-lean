# Polarity of a subformula occurrence

Let $A$ be a propositional formula built from atoms, $\bot$, $\wedge$, $\vee$ and $\to$. Each occurrence of a subformula $B$ in $A$ has a *polarity* in $\{+,-\}$, defined top-down: the occurrence of $A$ itself is positive; the immediate subformulas of an occurrence $C \wedge D$ or $C \vee D$ inherit its polarity; in an occurrence $C \to D$ the consequent $D$ inherits the polarity while the antecedent $C$ receives the opposite polarity. Thus an occurrence is positive exactly when it lies under an even number of antecedents of implications. (Negation $\neg C$ abbreviates $C \to \bot$, so it flips polarity.)

## Depends on

- [Truth-table evaluation](../../propositional-natural-deduction/eval-bool.md)

## Sources

- D. A. Plaisted and S. Greenbaum, "A Structure-Preserving Clause Form Translation", Journal of Symbolic Computation 2(3), 293–304, 1986.
