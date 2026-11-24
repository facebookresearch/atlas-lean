# Raw B-trees

A raw B-tree with keys in a type $\alpha$ is either a leaf, holding a list
of keys, or an internal node, holding a list of separator keys and a list of child raw B-trees.
The type imposes no invariant: that an internal node with $k$ keys has $k + 1$ children, the
bounds on key counts, the balance of the tree and the ordering of the keys are imposed
separately by the structural and ordering invariants of B-trees.
