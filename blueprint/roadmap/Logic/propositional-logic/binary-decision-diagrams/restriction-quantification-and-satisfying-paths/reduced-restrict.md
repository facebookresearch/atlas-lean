# Restriction yields a reduced diagram

For every binary decision diagram $t$, every
variable $x$ and every Boolean $b$, the cofactor $t[x := b]$ is reduced: no node has two equal
children.

Nodes that restriction keeps are rebuilt with the node constructor that removes redundant
tests, so the input need not be reduced.
