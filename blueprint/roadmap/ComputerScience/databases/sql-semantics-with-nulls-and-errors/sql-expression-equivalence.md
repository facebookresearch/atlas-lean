# Equivalence of SQL expressions is a congruence

Call expressions $e_1, e_2$ **equivalent** in context $\Gamma$ if on every row conforming to $\Gamma$ both fail or both succeed with the same datum (which error is raised is not observed, since strict evaluation fixes one of the evaluation orders SQL permits). This is an equivalence relation and a congruence for every expression constructor; it is compatible with renaming and with replacing substituted expressions by equivalent ones; and substituting into equivalent expressions preserves equivalence provided the substituted expressions are safe and have the column types. The side condition is necessary: $\mathsf{TRUE}$ and $x\ \mathsf{IS\ NULL\ OR}\ x\ \mathsf{IS\ NOT\ NULL}$ are equivalent, but substituting $1/0$ for $x$ makes only the second fail.

## Proof sketch

Reflexivity, symmetry and transitivity are immediate. Each constructor evaluates its operands strictly from left to right and returns the first error, and $\mathsf{CASE}$ evaluates its condition and then only the branch it takes, so replacing an operand by an equivalent one changes neither whether the evaluation fails nor the datum it returns; this is the congruence. Induction on an expression $e$ then shows that replacing each substituted $\sigma_i$ by an equivalent $\sigma'_i$ gives equivalent results. For substitution into equivalent expressions, first prove the substitution lemma by structural induction on $e$: if every $\sigma_i$ succeeds on a row $r$, then evaluating $e[\sigma]$ on $r$ equals evaluating $e$ on the row $(\sigma_1(r), \dots, \sigma_n(r))$ (column references by definition, literals and $\mathsf{NULL}$ unchanged, operators and $\mathsf{CASE}$ because their operands are evaluated in the same order with equal results). If $e_1, e_2$ are equivalent in $\Gamma$ and each $\sigma_i$ is safe of type $\Gamma(i)$, then on every conforming row each $\sigma_i$ succeeds with $\mathsf{NULL}$ or a value of type $\Gamma(i)$ by type soundness, so the row of results conforms to $\Gamma$, and by the lemma $e_1[\sigma]$ and $e_2[\sigma]$ behave as $e_1$ and $e_2$ on that row, hence alike. Renaming is the special case of substitution by column references, which always succeed.

## Depends on

- [Resolved SQL expressions and their evaluation](resolved-sql-expressions.md)
- [Typing and safety of SQL expressions](sql-expression-typing-and-safety.md)

## Proof depends on

- [Type soundness and safety for SQL expressions](sql-type-soundness.md)

## Sources

- P. Guagliardo and L. Libkin, "A Formal Semantics of SQL Queries, Its Validation, and Applications", Proceedings of the VLDB Endowment 11(1), 2017.
