# Entry Snapshot Permutation rejects wrong keyed payload

Anti-vacuity regression: the key projections are exactly equal, while the
second keyed payload changes from `20` to `99`; that payload-only corruption
does not satisfy the whole-entry snapshot invariant.
