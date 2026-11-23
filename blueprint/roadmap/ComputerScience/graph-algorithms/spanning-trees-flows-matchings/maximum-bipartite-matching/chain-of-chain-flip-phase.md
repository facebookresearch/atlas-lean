# Shortest chains from a vertex whose level a phase keeps were chains before it

Let $\mu$
be a valid partner array whose first free round is defined, and let $\mu'$ be obtained from $\mu$
by flipping all the paths of the phase of $\mu$. Let $z$ be a right vertex and $m$ a natural
number such that $z$ is first reached in round $m + 1$ of the layered search both for $\mu$ and
for $\mu'$, and let $S$ be an alternating chain for $\mu'$ from $z$ to an unmatched left vertex
with exactly $m + 1$ pairs. Then $S$ is also an alternating chain for $\mu$ from $z$ to an
unmatched left vertex, and for every pair of $S$ after the first, its right vertex is not the
right vertex of any pair on the paths of the phase.

A flipped edge would step back a round, which a chain of this length cannot afford.
