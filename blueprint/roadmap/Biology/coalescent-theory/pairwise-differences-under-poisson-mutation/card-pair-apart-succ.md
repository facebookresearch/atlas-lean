# Counting the histories that merge two apart genes at step $t$

Let `a` and `b` be genes of a sample of size `n`, let `t < n - 1` be a step, and write `N_t` for
the number of [ranked labeled histories](../ranked-labeled-histories-of-coalescent-trees/ranked-history.md) of
`n` genes in which the pair `{a, b}` is [apart](pair-apart.md) after `t` coalescence events.
Then `N_{t+1} · C(n - t, 2) + N_t = N_t · C(n - t, 2)`, where `C(n - t, 2) ≥ 1` is the number of
pairs of the `n - t` lineages present at step `t`. A pair apart after `t + 1` events
[is apart after `t` events](of-succ.md), so `N_t - N_{t+1}` counts the histories in which `a`
and `b` are apart after `t` events but not after `t + 1` events, those whose step `t` merges
their two lineages, and the identity says `N_t = (N_t - N_{t+1}) · C(n - t, 2)`: these histories
are a fraction `1 / C(n - t, 2)` of those in which `a` and `b` are apart after `t` events (when
there are any). For `a = b` both counts are `0`.
