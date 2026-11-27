# Quantifier-free formulas

For a first-order language $L$, a formula (with any number of bound variables in scope) is quantifier-free according to the recursion:

- $\bot$, every equation $t_1 = t_2$ and every relation atom $R(t_1, \dots, t_k)$ are quantifier-free;
- $\varphi \to \psi$ is quantifier-free if and only if both $\varphi$ and $\psi$ are;
- $\forall x\, \varphi$ is not quantifier-free.

Since the other connectives and $\exists$ are defined from $\bot$, $\to$ and $\forall$, a formula is quantifier-free exactly when it contains no quantifier.

## Sources

- Mathlib, `FirstOrder.Language.BoundedFormula.IsQF`, the same predicate on bounded formulas, https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/ModelTheory/Complexity.lean#L47-L74
