# Cubic expansion and finite group flows

Number the two ends of each edge of a finite loopless multigraph. A rotation system permutes the half-edges, preserves their incident vertex, has no fixed half-edge, and is transitive on the half-edges at each vertex. In the cubic expansion the vertices are the half-edges. Join the two ends of each original edge by a spoke, and for each half-edge add a distinct ring edge joining it to its chosen successor. A degree-two vertex produces two distinct parallel ring edges. An isolated vertex contributes no expanded vertex.

A flow with values in an additive abelian group assigns one value per oriented edge; at each vertex the sum at its numbered first ends minus the sum at its numbered second ends is zero. A nowhere-zero flow has nonzero value at every edge. Below the group $\Gamma=(\mathbb Z/2\mathbb Z)^3$ is written additively.

## Depends on

- [Circuits and double covers of finite loopless multigraphs](loopless-multigraph-circuit-cover.md)

## Expansion

Prove the orientation-change and cubic degree facts in the multigraph model. For a bridgeless graph verify existence of the specified rotations and preservation of bridgelessness under expansion; the two parallel ring edges at degree two must not be identified.

## Sources

- [Pinned rotation and expansion definitions](https://github.com/openai/cdc-lean/blob/577e9d9ea326d520f80672ee69b830bf1d513df5/CDCLean/Expansion.lean#L19-L27)
- [Pinned construction of the expansion](https://github.com/openai/cdc-lean/blob/577e9d9ea326d520f80672ee69b830bf1d513df5/CDCLean/Expansion.lean#L194-L265)
- [Pinned signed flows](https://github.com/openai/cdc-lean/blob/577e9d9ea326d520f80672ee69b830bf1d513df5/CDCLean/GeneralGraph.lean#L54-L77)
