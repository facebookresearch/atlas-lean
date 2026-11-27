# Reachability without an event

Let $a$ be an algorithm, $m$ a message and $s$, $t$ states. The state $t$ is reachable from $s$ without $m$ if some finite schedule leads from $s$ to $t$ by steps of $a$ and none of its steps receives $m$. In Lemma 3 of Fischer, Lynch and Paterson (1985) these states form the set $\mathcal{C}$ of configurations reachable from $C$ without applying the event $e = (p, m)$; if $m$ is in flight in $s$, it stays in flight in all of them, since only received messages leave the buffer.

## Sources

- M. J. Fischer, N. A. Lynch, M. S. Paterson, *Impossibility of distributed consensus with one faulty process*, Journal of the ACM 32(2), 1985, 374–382: Lemma 3.
