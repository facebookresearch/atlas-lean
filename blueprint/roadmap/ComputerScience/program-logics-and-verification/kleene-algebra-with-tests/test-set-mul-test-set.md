# Composing diagonal tests conjoins their assertions

Let $W$ be a set of states. Binary relations on $W$ are composed sequentially, $R \cdot S = \{(s, u) : (s, t) \in R \text{ and } (t, u) \in S \text{ for some } t\}$, with unit the identity relation $1$, and ordered by inclusion. For all assertions $P, Q \subseteq W$, the sequential composition of the [diagonal tests](test-set.md) of $P$ and $Q$ is the diagonal test of their conjunction: $[P] \cdot [Q] = [P \cap Q]$. Composing tests conjoins their assertions without changing the state.
