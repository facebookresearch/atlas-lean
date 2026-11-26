# Completed-path weight of a list of states

For stop probabilities $q$ and a survival kernel $Q$ on a set of states, the completed-path weight of a list of states is $0$ for the empty list, $q(x)$ for a one-element list $[x]$, and $Q(x, y)$ times the weight of $y :: \text{rest}$ for a list $x :: y :: \text{rest}$: the stop probability at the final state times the product of the survival-kernel entries along the list.
