# Cycle double cover from the nowhere-zero six-flow statement

Assume every finite bridgeless loopless multigraph admits an integer flow with $0<|f(e)|<6$ on each edge and signed conservation at each vertex. Under that assumption every finite bridgeless loopless multigraph has a cycle double cover. The premise is a single universal six-flow statement, not merely a flow supplied on the original graph.

## Depends on

- [Circuits and double covers of finite loopless multigraphs](loopless-multigraph-circuit-cover.md)
- [Cubic expansion and finite group flows](cubic-expansion-and-finite-group-flows.md)

## Proof depends on

- [Cycle double cover from a nowhere-zero flow on a cubic expansion](cycle-double-cover-from-eight-flow-on-expansion.md)

## Expansion

Apply the hypothesis on the bridgeless cubic expansion. Check that integer reduction modulo eight preserves conservation and nonzero labels, and formalize the coefficient-group transfer from cyclic order eight to the elementary abelian group of the same order. Then use the flow-to-cover implication.

## Sources

- [Pinned source: `cycleDoubleCover_of_sixFlow`](https://github.com/openai/cdc-lean/blob/577e9d9ea326d520f80672ee69b830bf1d513df5/CDCLean/Main.lean#L24-L28)
