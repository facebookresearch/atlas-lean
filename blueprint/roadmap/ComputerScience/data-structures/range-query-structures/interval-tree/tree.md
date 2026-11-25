# Interval tree

An interval tree is either empty or a node consisting of a left subtree,
an entry, a right subtree and three cached fields: a height and a size (natural numbers) and a
maximum high endpoint (an integer). The type imposes no balance or consistency condition on
these fields; it is the carrier on which the AVL interval-tree operations act.
