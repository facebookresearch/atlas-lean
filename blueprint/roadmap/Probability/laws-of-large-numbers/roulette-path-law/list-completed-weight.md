# Completed-path weight of a list of states

For real functions $q : S \to \mathbb{R}$ and $Q : S \times S \to \mathbb{R}$ on a set of states, the completed-path weight of a list of states is $0$ for the empty list, $q(x)$ for a one-element list $[x]$, and $Q(x, y)$ times the weight of $y :: \text{rest}$ for a list $x :: y :: \text{rest}$: the value at the final state times the product of the entries of $Q$ along the list. For stop probabilities $q$ and a survival kernel $Q$ it is the probability weight of stopping after exactly that list.
