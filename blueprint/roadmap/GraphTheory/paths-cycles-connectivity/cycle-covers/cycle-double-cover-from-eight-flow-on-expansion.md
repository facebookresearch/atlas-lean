# Cycle double cover from a nowhere-zero flow on a cubic expansion

Let $G$ be any finite loopless multigraph equipped with a rotation system $R$ as above. If the cubic expansion of $G$ using $R$ carries a nowhere-zero $\Gamma$-flow, then $G$ has a cycle double cover. There is no separate bridgelessness hypothesis on $G$ in this implication.

## Depends on

- [Circuits and double covers of finite loopless multigraphs](loopless-multigraph-circuit-cover.md)
- [Cubic expansion and finite group flows](cubic-expansion-and-finite-group-flows.md)

## Expansion

Check the affine-pair construction on all cubic vertex flow configurations, then prove that projection onto spokes preserves even incidence and exactly-two coverage for every original edge. Decompose each projected even set into edge-disjoint minimal nonempty circuits without collapsing repeated list entries. The proof must survive the multigraph and cover bridges.

## Sources

- [Pinned source: `cycleDoubleCover_of_gammaFlow`](https://github.com/openai/cdc-lean/blob/577e9d9ea326d520f80672ee69b830bf1d513df5/CDCLean/Main.lean#L44-L48)
