# Translation validation

Let $\mathrm{Validate}(S, C)$ be a checker, proved correct, that returns true only if the program $C$ has the same observable behavior as the program $S$ (for instance, a comparison of basic blocks by symbolic evaluation). Compose an unverified transformation $T$ with the check, so that the compiler emits $T(S)$ when $\mathrm{Validate}(S, T(S))$ holds. If it aborts otherwise, every program it does emit has the behavior of its input, whatever $T$ does; this preservation is conditional on the pass succeeding. If it instead falls back to a separately verified translation of $S$, it always emits a program and preservation is unconditional. When $T$ is an optimization within one language, emitting $S$ itself is such a fallback.

## Depends on

- [Notions of semantic preservation](notions-of-semantic-preservation.md)

## Proof depends on

- [Translation of a while language to a control-flow-graph IR](../intermediate-representations/translation-of-a-while-language-to-a-control.md)

## Sources

- X. Leroy, "Formal verification of a realistic compiler", *Communications of the ACM* 52(7):107–115, 2009
- A. Pnueli, M. Siegel and E. Singerman, "Translation validation", *TACAS 1998*, LNCS 1384, Springer, 1998
