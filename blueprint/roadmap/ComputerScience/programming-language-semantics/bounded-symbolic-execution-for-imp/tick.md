# Incrementing the cost of a symbolic path

A symbolic path is a record of a guard (a Boolean expression), a symbolic store $\sigma : \mathbb{N} \to \mathrm{AExp}$ (expressions over the initial state) and a cost $n \in \mathbb{N}$. Ticking a path $p$ gives the path with the same guard and store and cost one more than that of $p$.
