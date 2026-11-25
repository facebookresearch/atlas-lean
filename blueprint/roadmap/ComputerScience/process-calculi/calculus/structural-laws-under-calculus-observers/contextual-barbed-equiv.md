# Contextual strong barbed equivalence

Two π-calculus processes $P$ and $Q$ are contextually strong barbed equivalent when $C[P]$ and $C[Q]$ are [strongly barbed bisimilar](../strong-free-channel-barbed-bisimilarity/barbed-bisimilar.md) for every one-hole [context](context.md) $C$, with [lexical filling](fill.md). Lexical filling may capture dangling variables of $P$ and $Q$; it agrees with [capture-avoiding filling](fill-avoiding.md) when both are [scoped at depth $0$](../scope-preservation-for-calculus-names-and-proces/closed-at-2.md).
