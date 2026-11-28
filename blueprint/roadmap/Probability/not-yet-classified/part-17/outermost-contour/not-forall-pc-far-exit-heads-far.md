# Not forall pc Far Exit Heads Far

`pcFar_ExitHeadsFar` is not satisfied by every configuration with a finite origin cluster.
In `outC_upEdgeConfig` the cluster is `{(0, 0), (0, 1)}`: the right exit index is `0`, which
forces the box radius to be `0`, but `(0, 1)` is not in `[0, 0]²`. Hence every theorem assuming
`∀ ω hfin, pcFar_ExitHeadsFar ω hfin` is vacuous.
