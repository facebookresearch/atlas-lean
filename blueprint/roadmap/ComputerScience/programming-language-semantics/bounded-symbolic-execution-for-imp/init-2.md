# The initial symbolic path

A symbolic path is a record of a guard (a Boolean expression), a symbolic store $\sigma : \mathbb{N} \to \mathrm{AExp}$ (expressions over the initial state) and a cost $n \in \mathbb{N}$. The initial path has guard the literal true, the identity store $x \mapsto x$ (each variable mapped to itself) and cost $0$.
