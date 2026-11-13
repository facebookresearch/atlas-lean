# Splicing two red-black trees

The splice of a red-black tree $t$ with a red-black tree $s$ is
defined by recursion on $t$. The splice of the empty tree with $s$ is $s$. The splice of the node
with color $c$, left subtree $l$, key $k$ and right subtree $r$ with $s$ is the node with color
$c$, left subtree $l$, key $k$ and right subtree the splice of $r$ with $s$.

So $s$ becomes the right subtree of the rightmost node of $t$, and all existing colors are kept.
