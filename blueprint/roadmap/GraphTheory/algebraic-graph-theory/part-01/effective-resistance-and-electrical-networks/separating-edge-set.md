# Separating edge set (cutset)

Let $V$ and $E$ be finite sets and let each $e \in E$ be an edge from $e^-$ to $e^+$ in $V$ (a finite multigraph; loops $e^- = e^+$ are allowed). A set $P \subseteq E$ separates $a$ from $z$ if $z$ cannot be reached from $a$ along edges outside $P$ (traversed in either direction), so that every path from $a$ to $z$ uses an edge of $P$ (R. Lyons and Y. Peres, *Probability on Trees and Networks*, Cambridge University Press 2016, corrected online version of 19 August 2026, Section 2.5: a set $\Pi$ of edges separates $A$ and $Z$ if every path with one endpoint in $A$ and the other in $Z$ includes an edge in $\Pi$).

The source quantifies over paths; reachability along edges outside $P$ is the same condition, since any walk avoiding $P$ contains a path avoiding $P$. No edge set separates a vertex from itself, and the empty set separates $a$ from $z$ exactly when they lie in different components.
