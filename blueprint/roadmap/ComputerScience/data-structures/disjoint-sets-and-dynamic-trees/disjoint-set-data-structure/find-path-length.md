# Length of a find path

The number of parent pointers followed from a node $x$ to its root: the least $d$ with
$\mathrm{parent}^d(x) = \mathrm{root}(x)$ (an index that is not a node is its own parent and
root, so its find path length is $0$). The find path of $x$ has this many edges and one more
node, which is the cost charged to a find in this topic's cost model.
