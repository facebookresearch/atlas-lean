# One-step shift of the partial trajectory kernel

Let $\kappa$ be a Markov kernel on $S$
and $a, b \in \mathbb{N}$. For a history $z = (z_0, \dots, z_{a+b})$ of states in $S$, extend
$z$ by one step, drawing $z_{a+b+1}$ from $\kappa(z_{a+b}, \cdot)$, and then keep the entries
at times $a, \dots, a + b + 1$, reindexed as $0, \dots, b + 1$. The law of the result equals
the law obtained by first keeping the entries of $z$ at times $a, \dots, a + b$, reindexed as
$0, \dots, b$, and then extending that history by one step in the same way. This holds as an
identity of kernels in $z$.
