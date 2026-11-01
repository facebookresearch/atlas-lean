---
article_id: af_c48044dc3774c80d198584cf
declaration: def
origin: cited
lean: MetaMathlibExt.IsCompleteYoungGraph
---

# Is Complete Young Graph

`IsCompleteYoungGraph g k m`: the Young graph `Y(g, k)` is complete on
`m` nodes. Source: L. H. Kendrick, "Young Graphs: 1089 et al.", Journal of
Integer Sequences 18 (2015), stable source URL
`https://cs.uwaterloo.ca/journals/JIS/VOL18/Kendrick/ken1.tex`
(frozen source SHA-256
`28568ffc708329fe2de23639f32fd9f7a24a772a043deb40f9098c0f82e465c2`,
stable source ID `jis_grounded_3014355e4f55ef0bb856bf6f`).
Definition at lines 458-460 (quotation span SHA-256
`bac9fd74d3d31197005bee521a9d8070be41ed00fac48e0db94c1523bfea2625`):
in the source's `K_m` convention, the nodes other than the distinguished
starting node form the complete directed graph on `m` nodes, so the Young
graph has `m + 1` total nodes including that distinguished start; `[0, 0]`
is one of the `m` non-start nodes, and the starting node connects to every
node except `[0, 0]`.

## Depends on

This node has no prerequisites.

## Sources

- [WantedExt, WantedExt.NumberTheory.Digits.SloaneCompleteYoungGraphCharacterization](../../../../../../sources/v2/WantedExt.md)
