# Array lookup agrees with the timestamp list

For every execution and every natural
number $i$, the entry at index $i$ of the array of timestamps built by the vector clock algorithm
on the execution equals the $i$-th vector timestamp of the execution, where an index out of range
gives the zero vector in both lookups.
