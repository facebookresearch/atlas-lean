# Pulling a store fact out of a separating conjunction

Let $p$ be a predicate on
stores and $P$, $R$ heap assertions. Write $A \star B$ for the separating conjunction of heap
assertions $A$ and $B$ (the heap splits into two disjoint parts satisfying $A$ and $B$,
respectively, at the same store), and $p \land P$ for the heap assertion that holds at store
$s$ and heap $h$ when $p(s)$ and $P(s, h)$ both hold. Then
$(p \land P) \star R = p \land (P \star R)$.

This lets framed local triples be stated with the store facts kept outside the separating
conjunction.
