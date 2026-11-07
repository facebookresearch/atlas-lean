# Heap order of treap priorities

A tree is heap-ordered when the priority of every
node is at most the priority of every node below it. Recursively, the empty tree is
heap-ordered, and a node with priority $p$ is heap-ordered when its left and right subtrees
are heap-ordered and every node in them has priority at least $p$.
