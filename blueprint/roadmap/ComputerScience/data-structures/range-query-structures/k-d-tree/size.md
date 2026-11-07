# Size of a kd-tree

The size of a kd-tree is defined by recursion: the empty tree has
size $0$, a leaf has size $1$, and a split node has the sum of the sizes of its two
children. Since points are stored only at leaves, this is the number of points stored in the
tree, counted with multiplicity.
