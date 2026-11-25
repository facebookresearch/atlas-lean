# Fréchet derivative of a finite sum

Let $E$ and $F$ be normed spaces over a nontrivially normed field $K$, let
$x\in E$, and let $S$ be a finite subset of an index type. For each $i\in S$
let $f_i:E\to F$ have Fréchet derivative $A_i:E\to F$ at $x$, where $A_i$ is
continuous and $K$-linear. Then the pointwise sum $\sum_{i\in S}f_i$ has
Fréchet derivative $\sum_{i\in S}A_i$ at $x$. The result also applies when
$S$ is empty.

## Sources

- Mathlib, [`HasFDerivAt.sum`](https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/Analysis/Calculus/FDeriv/Add.lean#L416 "HasFDerivAt.sum").
