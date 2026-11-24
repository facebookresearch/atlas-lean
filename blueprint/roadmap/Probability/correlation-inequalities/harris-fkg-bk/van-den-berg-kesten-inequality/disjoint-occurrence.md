# Disjoint occurrence of events

Let $E$ be a set and $A, B \subseteq \{0,1\}^E$ events. Their *disjoint occurrence* $A \mathbin{\square} B$ is the set of configurations $\omega$ for which there are disjoint sets $K, L \subseteq E$ such that $A$ [occurs on](occurs-on.md) $K$ at $\omega$ and $B$ occurs on $L$ at $\omega$:

$$A \mathbin{\square} B = \{\omega : \exists K, L \subseteq E,\ K \cap L = \emptyset,\ A \text{ occurs on } K \text{ at } \omega,\ B \text{ occurs on } L \text{ at } \omega\}.$$
