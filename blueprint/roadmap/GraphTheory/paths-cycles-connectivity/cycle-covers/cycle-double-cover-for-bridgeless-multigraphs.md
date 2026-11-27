# Cycle double cover for bridgeless loopless multigraphs

Every finite bridgeless loopless multigraph has a finite list of circuits such that each edge belongs to exactly two entries. Bridgelessness allows disconnected and edgeless graphs, and circuits of length two are allowed for parallel edges. No six-flow theorem is an explicit hypothesis of this endpoint.

The source is the pinned formal development. Its mathematical interpretation depends on the edge-object, cut, and circuit conventions, not on identifying the carrier with simple graphs or treating the list as a set.

## Depends on

- [Circuits and double covers of finite loopless multigraphs](loopless-multigraph-circuit-cover.md)

## Proof depends on

- [Cycle double cover from a nowhere-zero flow on a cubic expansion](cycle-double-cover-from-eight-flow-on-expansion.md)

## Expansion

Independently check the cut-to-bridge and circuit-to-cycle correspondences and the translation to the conventional multigraph conjecture. Recheck the cubic expansion and its bridgelessness, the nowhere-zero eight-flow input and the projected affine-pair double cover. In particular, audit that the source discharges the eight-flow premise without any project axiom before giving proof credit.

## Sources

- [Pinned verification description](https://github.com/openai/cdc-lean/blob/577e9d9ea326d520f80672ee69b830bf1d513df5/VERIFICATION.md#L1-L29)
- [Pinned source: `cycleDoubleCover_of_bridgeless`](https://github.com/openai/cdc-lean/blob/577e9d9ea326d520f80672ee69b830bf1d513df5/CDCLean/Main.lean#L58-L61)
