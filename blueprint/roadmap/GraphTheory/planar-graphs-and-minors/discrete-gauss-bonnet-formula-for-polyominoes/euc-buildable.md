# Cell regions built by attaching cells along boundary arcs

The class of buildable finite sets of unit cells is defined inductively:

- every one-cell set $\{c\}$ is buildable;
- if $K$ is buildable and $c \notin K$ is a cell such that the number of sides of $c$ that are not sides of cells of $K$ exceeds by exactly one the number of corners of $c$ that are not corners of cells of $K$, then $K \cup \{c\}$ is buildable.

Every buildable set $K$ has Euler characteristic $V - E + F = 1$, where $V$ and $E$ are the numbers of distinct corners and sides of its cells and $F = |K|$.
