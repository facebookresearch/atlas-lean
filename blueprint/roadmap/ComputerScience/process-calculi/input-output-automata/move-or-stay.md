# Component move in a composition

Let $A$ be an [input/output automaton](ioautomaton.md), $s$ and $t$ states of $A$ and $a$ an action. The component $A$ moves from $s$ to $t$ on $a$ when either $a$ is an action of $A$ and $s \xrightarrow{a} t$ is a transition of $A$, or $a$ is not an action of $A$ and $t = s$.
