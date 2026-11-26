# Razborov: supercritical trade-off between width and tree-like size

For every constant $k \ge 1$ there are unsatisfiable $O(1)$-CNF formulas $F_n$ on $n$ variables that have resolution refutations of width $w = o(n)$, such that every tree-like resolution refutation of $F_n$ whose width is at most a constant factor above $w$ has size $2^{\omega(n)}$, exceeding the trivial $2^{O(n)}$ upper bound for tree-like refutations without width restriction. Thus restricting to near-minimal width forces tree-like size beyond the worst case.

## Proof sketch

Construct $F_n$ by composing a formula of small width with a hardness condensation transformation that compresses many variables into few via an expanding substitution: any narrow refutation of the condensed formula must simulate a narrow refutation of the original with many variables, inheriting a tree-size lower bound in terms of the original number of variables, which is polynomially larger than $n$.

## Depends on

- [Supercritical trade-offs in proof complexity](supercritical-tradeoff.md)

## Proof depends on

- [Ben-Sasson–Wigderson for tree-like resolution](../../propositional-logic/resolution-size-and-width/tree-refutation-narrow.md)

## Sources

- A. A. Razborov, "A new kind of tradeoffs in propositional proof complexity", Journal of the ACM 63 (2016).
