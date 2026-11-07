# Sparse table

A sparse table over a type $\alpha$ consists of an array of elements of
$\alpha$, called its data, and an array of arrays of elements of $\alpha$, called its levels.

The intended meaning is that level $k$ stores the minima of the length-$2^k$ slices of the data;
data and levels are stored as arrays so that entry lookup is random access. Arbitrary values need
not relate data and levels at all; validity ties every stored level to this specification, tables
produced by the construction are valid, and query correctness is stated for valid tables.
