# Siphons and traps

Let $N$ be an ordinary [Petri net](place-transition-petri-nets.md). For a set $S$ of places let ${}^\bullet S$ and $S^\bullet$ be the sets of transitions with an output place in $S$ and with an input place in $S$. A nonempty set of places $S$ is a *siphon* if ${}^\bullet S \subseteq S^\bullet$: every transition with an output place in $S$ has an input place in $S$. A nonempty set of places $Q$ is a *trap* if $Q^\bullet \subseteq {}^\bullet Q$: every transition with an input place in $Q$ has an output place in $Q$. A trap $Q$ is *marked* at $M_0$ if $M_0(p) > 0$ for some $p \in Q$.

## Depends on

- [Place/transition Petri nets](place-transition-petri-nets.md)

## Sources

- T. Murata, "Petri nets: Properties, analysis and applications", *Proceedings of the IEEE* 77(4):541–580, 1989, Section VI-B, item 3), the definitions of siphon and trap.
