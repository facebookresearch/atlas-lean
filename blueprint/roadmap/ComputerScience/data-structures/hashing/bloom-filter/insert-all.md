# Inserting a list of elements into a Bloom filter

Inserting a list $[x_1, \dots, x_r]$ into a Bloom filter $F$ means inserting $x_1$ into $F$, then
$x_2$ into the result, and so on up to $x_r$; inserting the empty list leaves $F$ unchanged.
