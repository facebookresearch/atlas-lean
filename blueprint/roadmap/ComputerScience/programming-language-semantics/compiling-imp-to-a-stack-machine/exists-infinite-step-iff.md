# An IMP configuration has an infinite small-step execution exactly when it has no big-step result

IMP configurations are pairs $(c, s)$ of a command and a state, and $\to$ is the small-step relation on them. For every command $c$ and state $s$, there is a sequence $(g_n)_{n \in \mathbb{N}}$ of configurations with $g_0 = (c, s)$ and $g_n \to g_{n+1}$ for every $n$ if and only if for every state $s'$, $c$ run from $s$ does not terminate in $s'$ under the big-step semantics.
