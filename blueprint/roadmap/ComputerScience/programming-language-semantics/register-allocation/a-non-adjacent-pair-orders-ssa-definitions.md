# A non-adjacent pair orders SSA definitions

Let $P$ be a strict program in SSA form with interference graph $G = (V, E)$, as in [interference in strict SSA programs](interference-in-strict-ssa-programs.md). Let $ab \in E$ and $bc \in E$ but $ac \notin E$. If $D_a$ dominates $D_b$, then $D_b$ strictly dominates $D_c$.

**Proof.** By [the comparability lemma](interfering-ssa-variables-have-comparable-defi.md), $D_b$ and $D_c$ are comparable. If $D_c$ dominated $D_b$, then by [the liveness lemma](the-earlier-of-two-interfering-ssa-variables.md) both $c$ and $a$ would be live at $D_b$, so $a$ and $c$ would interfere.

## Depends on

- [Interference in strict SSA programs](interference-in-strict-ssa-programs.md)

## Proof depends on

- [Interfering SSA variables have comparable definitions](interfering-ssa-variables-have-comparable-defi.md)
- [The earlier of two interfering SSA variables is live at the later definition](the-earlier-of-two-interfering-ssa-variables.md)

## Sources

- S. Hack, D. Grund and G. Goos, "Register allocation for programs in SSA-form", *Compiler Construction (CC 2006)*, LNCS 3923, Springer, 2006, pp. 247–262, <https://compilers.cs.uni-saarland.de/papers/ssara.pdf>, Section 3, Lemma 3 with its proof (stated there as the dominance of $D_b$ over $D_c$; the proof excludes that $D_c$ dominates $D_b$).
