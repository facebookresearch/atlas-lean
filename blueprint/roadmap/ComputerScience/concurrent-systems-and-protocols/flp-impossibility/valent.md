# Valence of a state

Let $a$ be an algorithm, $s$ a state and $b$ a decision value (false or true). The value $b$ is a valence of $s$ for $a$ if some state reachable from $s$ by finitely many steps of $a$ has decided $b$, that is, some process has output $b$ in it. In the terms of Fischer, Lynch and Paterson (1985, §3), $b$ belongs to the set $V$ of decision values of the configurations reachable from $s$; $s$ is bivalent when $|V| = 2$ and $b$-valent when $V = \{b\}$.

## Sources

- M. J. Fischer, N. A. Lynch, M. S. Paterson, *Impossibility of distributed consensus with one faulty process*, Journal of the ACM 32(2), 1985, 374–382: §3.
