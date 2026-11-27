# Lexicographic path ordering

Let $\Sigma$ be a finite signature and $\succ$ a strict partial ordering on its function symbols, the *precedence*. The *lexicographic path ordering* $\succ_{\mathrm{lpo}}$ on $T_\Sigma(X)$ induced by $\succ$ is defined by: $s \succ_{\mathrm{lpo}} t$ if

1. $t \in \mathrm{var}(s)$ and $t \ne s$, or
2. $s = f(s_1, \dots, s_m)$, $t = g(t_1, \dots, t_n)$, and
   - (a) $s_i \succeq_{\mathrm{lpo}} t$ for some $i$, or
   - (b) $f \succ g$ and $s \succ_{\mathrm{lpo}} t_j$ for all $j$, or
   - (c) $f = g$, $s \succ_{\mathrm{lpo}} t_j$ for all $j$, and $(s_1, \dots, s_m) \mathrel{(\succ_{\mathrm{lpo}})_{\mathrm{lex}}} (t_1, \dots, t_n)$,

where $\succeq_{\mathrm{lpo}}$ is the reflexive closure and $(\succ_{\mathrm{lpo}})_{\mathrm{lex}}$ the $m$-fold lexicographic combination of $\succ_{\mathrm{lpo}}$, comparing argument lists left to right ($f = g$ forces $m = n$).

## Depends on

- [Term rewriting systems](../automated-deduction/term-rewriting-systems.md)
- [Unification of ranked terms through the curried encoding](../first-order-unification/unification-of-ranked-terms-through-the-curried-encoding.md)

## Sources

- U. Waldmann, *Automated Reasoning*, lecture notes, Max Planck Institute for Informatics, winter semester 2019/20, <https://rg1-teaching.mpi-inf.mpg.de/autrea-ws19/script.pdf>, Section 4.5, path orderings, pp. 119–120 (Kamin and Lévy).
