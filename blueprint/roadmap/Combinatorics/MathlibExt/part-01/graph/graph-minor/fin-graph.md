---
article_id: af_b688b4e1a50828a662125f81
declaration: structure
origin: cited
statement: formalized
lean: MetaMathlibExt.FinGraph
---

# Fin Graph

Bundled finite simple graph: a vertex type together with its finiteness
witness and a simple graph on it. The witness is an instance-implicit field,
so it is synthesized by typeclass search at construction; downstream code
still accesses it explicitly as `G.fin`, since instances cannot depend on a
locally bound graph.
Stable source: https://en.wikipedia.org/wiki/Robertson%E2%80%93Seymour_theorem.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Combinatorics.Graph.GraphMinor](../../../../../../sources/v2/MathlibExt.md)
