# A pair apart after the next event was already apart

Let `h` be a [ranked labeled history](../ranked-labeled-histories-of-coalescent-trees/ranked-history.md) of `n`
genes, `a` and `b` genes and `t` a natural number. If the pair `{a, b}` is
[apart](pair-apart.md) after `t + 1` coalescence events, then it is apart after `t` events.
Equivalently, if `a` and `b` are in one lineage after `t` events, they are still in one lineage
after `t + 1` events. Iterating this one step gives the statements for any `t ≤ u`:
[apart after `u` events implies apart after `t` events](pair-apart-of-le.md), and
[together after `t` events implies together after `u` events](not-pair-apart-of-le.md).
