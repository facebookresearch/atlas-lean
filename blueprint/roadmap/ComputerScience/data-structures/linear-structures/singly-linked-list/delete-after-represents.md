# Deleting a successor removes it from the represented list

Fix a capacity $n$, let $s$ be a
store assigning to each identity below $n$ either nothing or a singly linked list node, and
suppose that $s$ with head $h$ represents the list of identities $L = (i_0, \dots, i_{m-1})$. Let
$k < m$ be such that $s(i_k)$ is a node, and let $s'$ be the store obtained from $s$ by deleting
the successor of $i_k$. Then $s'$ with the same head $h$ represents the list obtained from $L$ by
removing the entry at position $k + 1$. Positions count from $0$, and at the tail ($k + 1 = m$)
the list is unchanged.
