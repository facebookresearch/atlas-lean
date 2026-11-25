# Sentinel insertion takes four steps

Let $S$ be a store of $n$ cells, each empty or holding
a node, in which the cells $x$ and $y$ are allocated, the next pointer of $y$ is not NIL, and the
cell it points to is allocated. Then sentinel insertion of $x$ after $y$ in $S$ costs exactly $4$
time units, one per pointer assignment.

This counts logical pointer assignments, not full RAM cost.
