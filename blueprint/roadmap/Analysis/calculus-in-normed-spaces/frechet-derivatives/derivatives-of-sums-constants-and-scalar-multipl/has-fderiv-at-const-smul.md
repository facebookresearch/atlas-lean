# Fréchet derivative of a constant scalar multiple

Let $E$ and $F$ be normed spaces over a nontrivially normed field $K$. Let a
monoid $R$ act on $F$ by additive maps, with the action commuting with
$K$-scalar multiplication and with $y\mapsto c\cdot y$ continuous for each
$c\in R$. Suppose $f:E\to F$ has Fréchet derivative $A:E\to F$ at $x\in E$,
where $A$ is continuous and $K$-linear. Then for every constant $c\in R$,
$y\mapsto c\cdot f(y)$ has Fréchet derivative $h\mapsto c\cdot A(h)$ at $x$.
There is no invertibility assumption on $c$.

## Sources

- Mathlib, [`HasFDerivAt.const_smul`](https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/Analysis/Calculus/FDeriv/Add.lean#L65 "HasFDerivAt.const_smul").
