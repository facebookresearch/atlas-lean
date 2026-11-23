# Insertion into a represented singly linked list

Suppose the store $S$ with head $h$
represents the list of distinct identities $(i_0, \dots, i_{m-1})$. Let $k < m$, assume that the
store entry of $i_k$ is a node, and let $x$ be an identity whose store entry is a node and which
is not among $i_0, \dots, i_{m-1}$. Then the store obtained by inserting $x$ after $i_k$, with
the same head $h$, represents the list $(i_0, \dots, i_k, x, i_{k+1}, \dots, i_{m-1})$.
