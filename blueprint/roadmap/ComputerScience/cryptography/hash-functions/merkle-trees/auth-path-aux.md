# Siblings on the way up

Starting from position $i$ of a level, the siblings met on the way up for $k$ levels are the sibling
of $i$ (the node at position $i + 1$ if $i$ is even, and at $i - 1$ if $i$ is odd), followed by the
siblings met from position $\lfloor i/2 \rfloor$ of the next level. A promoted node has no sibling and
contributes nothing.
