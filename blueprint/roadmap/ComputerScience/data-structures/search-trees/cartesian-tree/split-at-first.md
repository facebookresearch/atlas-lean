# Splitting a list at the first occurrence of a value

For a value $m$ of a type with
decidable equality and a list $xs$, the split of $xs$ at $m$ is the pair of the part of $xs$
before the first occurrence of $m$ and the part after it; that occurrence itself is dropped. If
$m$ does not occur in $xs$, the split is the pair of $xs$ and the empty list.

Only equality on the element type is needed, not the linear order required to build Cartesian
trees.
