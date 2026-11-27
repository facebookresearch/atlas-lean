# Typing substituted terms with intersections

Let $\vdash$ be typing in [system D](intersection-type-system-d.md) or [system DΩ](intersection-type-system-d-omega.md), $\Gamma$ a context and $x_1, \dots, x_k$ variables not declared in $\Gamma$.

1. (substitution) If $\Gamma, x_1 : A_1, \dots, x_k : A_k \vdash u : B$ and $\Gamma \vdash t_i : A_i$ for every $x_i$ free in $u$, then $\Gamma \vdash u[t_1/x_1, \dots, t_k/x_k] : B$.
2. (inverse substitution) If $\Gamma \vdash u[t_1/x_1, \dots, t_k/x_k] : B$ and each $t_i$ is typable in $\Gamma$, then there are types $A_1, \dots, A_k$ with $\Gamma \vdash t_i : A_i$ and
   $\Gamma, x_1 : A_1, \dots, x_k : A_k \vdash u : B$. In particular, if $\Gamma \vdash u[t/x] : B$ and $t$ is typable in $\Gamma$, then $\Gamma \vdash (\lambda x.\, u)\, t : B$.

In DΩ every term is typable (with type $\Omega$), so the typability hypotheses hold automatically. The second part is where intersections are needed: the
occurrences of $t_i$ in $u[t_1/x_1, \dots]$ may be typed differently, and $A_i$ is the intersection of their types; when $x_i$ does not occur in $u$, $A_i$ is any type of $t_i$ (D has no empty
intersection).

## Depends on

- [The intersection type system D](intersection-type-system-d.md)
- [The intersection type system DΩ](intersection-type-system-d-omega.md)

## Sources

- J.-L. Krivine, *Lambda-Calculus, Types and Models*, translated from the French by R. Cori, revised online edition, 2011, <https://www.irif.fr/~krivine/articles/Lambda.pdf>: Chapter 4, Proposition 4.1, Proposition 4.4 with its remarks, and Corollary 4.5.
