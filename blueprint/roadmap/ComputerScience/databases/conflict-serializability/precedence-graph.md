# Precedence graph

The precedence (serialization) graph of a schedule $s$ of $n$
transactions is the directed adjacency graph whose vertices are the transactions
$0, \dots, n - 1$, listed in increasing order, and whose adjacency list at a transaction $i$ lists,
in increasing order, the transactions $j$ such that there is a precedence edge from $i$ to $j$
in $s$.
