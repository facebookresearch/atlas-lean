---
article_id: af_8e9803ce03dc36e97a796cdf
declaration: theorem
origin: cited
statement: formalized
lean: MetaMathlibExt.sloane_complete_young_graph_characterization
---

# Sloane complete young graph characterization

Sloane complete Young graph characterization: Corollary at lines 574-576
(quotation span SHA-256
`a7c50f9bea3cb4b958aecdbee7b56879d930178eae594729d8e54e36b7767395`)
of L. H. Kendrick, "Young Graphs: 1089 et al.", Journal of Integer
Sequences 18 (2015), stable source URL
`https://cs.uwaterloo.ca/journals/JIS/VOL18/Kendrick/ken1.tex`
(frozen source SHA-256
`28568ffc708329fe2de23639f32fd9f7a24a772a043deb40f9098c0f82e465c2`,
stable source ID `jis_grounded_3014355e4f55ef0bb856bf6f`):
under `2 ≤ k < g`, `Y(g, k)` is complete on `m` nodes iff
`⌊gcd(g - k, k ^ 2 - 1) / (k + 1)⌋ = m - 1`. In the source's `K_m`
convention, the nodes other than the distinguished starting node form the
complete directed graph on `m` nodes, so the Young graph has `m + 1` total
nodes including that distinguished start; `[0, 0]` is one of the `m`
non-start nodes. Natural-number division represents the source floor
because all quantities are nonnegative and the denominator is positive.

The hypothesis is `2 ≤ m`, not `1 ≤ m`. The corollary rests on Theorem
`thm:completegraph`, whose proof starts "Since $s_1$ exists", so it needs
`m - 1 ≥ 1`. For `m = 1` the class `K_1` contains no Young graph: every Young
graph is connected and contains `[0, 0]`, so the starting node has an edge to
some node other than `[0, 0]` (proof of Theorem `thm:0iso`), while a graph in
`K_1` has none. With `1 ≤ m`, `(g, k) = (10, 9)` and `m = 1` give
`gcd(1, 80) / 10 = 0 = m - 1`, but `Y(10, 9)` is the 1089 graph, not in `K_1`.

## Depends on

This node has no prerequisites.

## Sources

- [WantedExt, WantedExt.NumberTheory.Digits.SloaneCompleteYoungGraphCharacterization](../../../../../../sources/v2/WantedExt.md)
