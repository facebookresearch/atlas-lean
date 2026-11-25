# Leftist invariant with correct stored ranks

The leftist invariant of a leftist heap is defined recursively: the empty heap satisfies it, and
a node $\langle k, x, \ell, r \rangle$ satisfies it exactly when

- $k$ equals the rank of $r$ plus $1$;
- the rank of $\ell$ is at least the rank of $r$;
- $\ell$ and $r$ both satisfy the leftist invariant.

Here the rank of a heap is $0$ for the empty heap and the stored rank of the root otherwise.
