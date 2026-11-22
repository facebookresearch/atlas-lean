# Lexical filling of a process context

The lexical filling $C[P]$ of a [context](context.md) $C$ with a process $P$ replaces the hole of $C$ by $P$, unchanged: $[\,][P] = P$, and filling commutes with every constructor ($(\nu C)[P] = \nu\,(C[P])$, $(a(\cdot).C)[P] = a(\cdot).C[P]$, $(C \mid Q)[P] = C[P] \mid Q$, and so on). Free channels of $P$ are never captured, and a process [scoped at depth $0$](../scope-preservation-for-calculus-names-and-proces/closed-at-2.md) has no references into the surrounding binders; other variables of $P$ may be captured by binders of $C$.
