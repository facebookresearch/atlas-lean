# Dependency pairs

Let $R$ be a [term rewriting system](../../automated-deduction/term-rewriting-systems.md) over a signature $\mathcal F$. Its *defined symbols* $D$ are the root symbols of left-hand sides of rules, and the other symbols are *constructors*. Extend the signature by a fresh *tuple symbol* $F$ for each defined symbol $f$, of the same arity. If $f(s_1, \dots, s_n) \to C[g(t_1, \dots, t_m)]$ is a rule of $R$, $C$ a context and $g$ a defined symbol, then $\langle F(s_1, \dots, s_n), G(t_1, \dots, t_m)\rangle$ is a *dependency pair* of $R$. A finite system has finitely many dependency pairs.

For example, the rules $\mathit{minus}(x, 0) \to x$, $\mathit{minus}(s(x), s(y)) \to \mathit{minus}(x, y)$, $\mathit{quot}(0, s(y)) \to 0$ and $\mathit{quot}(s(x), s(y)) \to s(\mathit{quot}(\mathit{minus}(x, y), s(y)))$ have the dependency pairs $\langle M(s(x), s(y)), M(x, y)\rangle$, $\langle Q(s(x), s(y)), M(x, y)\rangle$ and $\langle Q(s(x), s(y)), Q(\mathit{minus}(x, y), s(y))\rangle$.

## Depends on

- [Term rewriting systems](../../automated-deduction/term-rewriting-systems.md)

## Sources

- T. Arts and J. Giesl, "Termination of term rewriting using dependency pairs", *Theoretical Computer Science* 236(1–2):133–178, 2000, <https://verify.rwth-aachen.de/giesl/papers/TCS-distribute.pdf>, Section 2.1: Definition 1 (defined symbols and constructors), Example 2, Definition 3 (dependency pairs, with tuple symbols) and Example 4.
