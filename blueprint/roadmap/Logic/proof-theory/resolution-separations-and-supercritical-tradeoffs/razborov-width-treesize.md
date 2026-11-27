# Razborov: supercritical trade-off between width and tree-like size

Let $k = k(n) \ge 4$ and let $\varepsilon > 0$ be a constant. There are unsatisfiable $k$-CNF formulas $\tau_n$ on $n$ variables that have resolution refutations of width $O(k)$, such that every tree-like resolution refutation of $\tau_n$ of width at most $n^{1-\varepsilon}/k$ has size $\exp(n^{\Omega(k)})$. For constant $k$ large enough this exceeds $2^{n+1}$, a size within which every unsatisfiable CNF on $n$ variables has a tree-like refutation, although the width allowed is far above the minimum.

## Proof sketch

Construct $\tau_n$ by composing a formula of small width with a hardness condensation transformation that compresses many variables into few via an expanding substitution: any narrow refutation of the condensed formula must simulate a narrow refutation of the original with many variables, inheriting a tree-size lower bound in terms of the original number of variables, which is polynomially larger than $n$.

## Depends on

- [Supercritical trade-offs in proof complexity](supercritical-tradeoff.md)

## Proof depends on

- [Ben-Sasson–Wigderson for tree-like resolution](../../propositional-logic/resolution-size-and-width/tree-refutation-narrow.md)

## Sources

- A. A. Razborov, "A new kind of tradeoffs in propositional proof complexity", Journal of the ACM 63 (2016).
