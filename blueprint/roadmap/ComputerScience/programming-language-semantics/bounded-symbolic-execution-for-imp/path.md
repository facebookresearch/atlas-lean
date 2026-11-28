# Symbolic paths of IMP symbolic execution

A symbolic path is a record of a guard (a Boolean expression), a symbolic store $\sigma : \mathbb{N} \to \mathrm{AExp}$ (expressions over the initial state) and a cost $n \in \mathbb{N}$. The guard is the path condition accumulated so far, and the cost counts loop-body entries.
