# Serialization of a schedule along a transaction order

For a list $\sigma$ of transactions
and a schedule $s$, the serialization of $s$ along $\sigma$ sorts the operations of $s$ by the
position of the first occurrence of their transaction in $\sigma$, where a transaction that does
not occur in $\sigma$ gets the length of $\sigma$ as its position. The sort is stable: operations
with the same position keep their relative order in $s$.
