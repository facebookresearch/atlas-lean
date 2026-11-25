# Hoare validity embeds into separation validity

Let $P$ and $Q$ be store assertions and
$c$ a command of plain IMP. If the partial-correctness Hoare triple with precondition $P$, command
$c$ and postcondition $Q$ is valid, then the separation-logic triple for the embedding of $c$ into
heap IMP is valid with the precondition that holds of a store $s$ and any heap exactly when $P(s)$
holds and the postcondition that holds of a store $s$ and any heap exactly when $Q(s)$ holds.

Embedded commands are always safe, never change the heap, and terminate exactly when the plain
command does.
