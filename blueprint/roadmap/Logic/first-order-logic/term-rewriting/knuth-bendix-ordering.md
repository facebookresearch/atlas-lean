# Knuth–Bendix ordering

Let $\Sigma$ be a finite signature, $\succ$ a strict partial ordering (precedence) on its function symbols and $w : \Sigma \cup X \to \mathbb R_{\ge 0}$ a weight function satisfying the *admissibility conditions*: $w(x) = w_0 > 0$ for every variable $x$; $w(c) \ge w_0$ for every constant $c$; and if $w(f) = 0$ for a unary symbol $f$, then $f \succ g$ for every other function symbol $g$. Extend $w$ to terms by $w(f(t_1, \dots, t_n)) = w(f) + \sum_{i=1}^n w(t_i)$, and write $\#(x, t)$ for the number of occurrences of $x$ in $t$.

The *Knuth–Bendix ordering* $\succ_{\mathrm{kbo}}$ on $T_\Sigma(X)$ induced by $\succ$ and $w$ is defined by: $s \succ_{\mathrm{kbo}} t$ if $\#(x, s) \ge \#(x, t)$ for every variable $x$ and either

1. $w(s) > w(t)$, or
2. $w(s) = w(t)$ and
   - (a) $t = x$ and $s = f^n(x)$ for a variable $x$, a unary symbol $f$ and some $n \ge 1$, or
   - (b) $s = f(s_1, \dots, s_m)$, $t = g(t_1, \dots, t_n)$ and $f \succ g$, or
   - (c) $s = f(s_1, \dots, s_m)$, $t = f(t_1, \dots, t_m)$ and $(s_1, \dots, s_m) \mathrel{(\succ_{\mathrm{kbo}})_{\mathrm{lex}}} (t_1, \dots, t_m)$.

## Depends on

- [Term rewriting systems](../automated-deduction/term-rewriting-systems.md)
- [Unification of ranked terms through the curried encoding](../first-order-unification/unification-of-ranked-terms-through-the-curried-encoding.md)

## Sources

- U. Waldmann, *Automated Reasoning*, lecture notes, Max Planck Institute for Informatics, winter semester 2019/20, <https://rg1-teaching.mpi-inf.mpg.de/autrea-ws19/script.pdf>, Section 4.5, the Knuth–Bendix ordering, p. 121.
