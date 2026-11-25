# Bivalent state

Let $a$ be an algorithm and $s$ a state. The state $s$ is bivalent for $a$ if both decision values are valences of $s$ ([Valence of a state](valent.md)): some state reachable from $s$ by steps of $a$ has decided false, and some state reachable from $s$ has decided true (Fischer, Lynch and Paterson, 1985, §3). The impossibility proof keeps a run in bivalent states forever.

## Background

- [Valence of a state](valent.md): the definition is that both values are valences.

## Sources

- M. J. Fischer, N. A. Lynch, M. S. Paterson, *Impossibility of distributed consensus with one faulty process*, Journal of the ACM 32(2), 1985, 374–382: §3.
