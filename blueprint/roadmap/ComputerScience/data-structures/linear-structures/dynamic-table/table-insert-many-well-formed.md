# Repeated insertion preserves well-formedness of a dynamic table

Call a dynamic table
with item count $n$ well formed when, for every slot index $i$, slot $i$ is occupied exactly
when $i < n$. If a dynamic table $T$ is well formed, then for every array $xs$, the table
obtained from $T$ by inserting the entries of $xs$ one at a time with TABLE-INSERT, in array
order, is again well formed.
