# Rearranging a separating conjunction

For heap assertions $P$, $Q$ and $R$, write
$A \star B$ for the separating conjunction of heap assertions $A$ and $B$ (the heap splits into
two disjoint parts satisfying $A$ and $B$, respectively, at the same store). Then
$P \star (Q \star R)$ entails $(P \star R) \star Q$: every store and heap satisfying the first
assertion satisfy the second.
