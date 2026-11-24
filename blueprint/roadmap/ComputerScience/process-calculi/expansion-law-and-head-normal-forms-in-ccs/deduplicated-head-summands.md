# Deduplicated head summands of a static CCS process

Let the channel names form a type with decidable equality. For a static CCS process $P$, its deduplicated head summands are the list of its head summands $h(P)$ with repeated entries removed: summands are compared by syntactic equality of action and continuation, the last occurrence of each entry is kept, and the kept entries stay in their relative order. The result is generally not a canonical representative of the strong bisimilarity class of $P$, since the order of the entries and the syntax of the continuations depend on $P$.
