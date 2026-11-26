# Survival weight of a fixed-length path

For a real function $Q$ on $S \times S$ and a path $x = (x_0, \dots, x_n)$ of $n + 1$ states, the survival weight of $x$ is $\prod_{k<n} Q(x_k, x_{k+1})$, the product of the entries of $Q$ along its $n$ transitions. It is a raw real weight, with no sign or row condition: for one state with $Q(i,i) = -2$, the path $(i, i)$ has survival weight $-2$. When $Q$ is a survival kernel (nonnegative entries), it is the probability of following $x$ without stopping, given its start.
