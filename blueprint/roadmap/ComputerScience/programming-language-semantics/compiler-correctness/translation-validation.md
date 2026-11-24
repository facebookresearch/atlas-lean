# Translation validation

Let $\mathrm{Validate}(S, C)$ be a checker, proved correct, that returns true only if the program $C$ has the same observable behavior as the program $S$ (for instance, a comparison of basic blocks by symbolic evaluation). Composing an unverified transformation $T$ with the check, so that the compiler emits $T(S)$ when $\mathrm{Validate}(S, T(S))$ holds and $S$ otherwise, gives a pass that always preserves the behavior of its input, whatever $T$ does.

## Proof depends on

- [Translation of a while language to a control-flow-graph IR](../intermediate-representations/translation-of-a-while-language-to-a-control.md)

## Expansion

This page becomes ready once these prerequisites are stated:

- Observable behaviors and notions of semantic preservation (statement prerequisite; formal statement exists, page pending)

## Sources

- X. Leroy, "Formal verification of a realistic compiler", *Communications of the ACM* 52(7):107–115, 2009
- A. Pnueli, M. Siegel and E. Singerman, "Translation validation", *TACAS 1998*, LNCS 1384, Springer, 1998
