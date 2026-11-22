# Building an AVL tree from a list

For a linearly ordered type $\alpha$, the tree built
from the empty list is the empty tree, and the tree built from a list with head $x$ and tail
$xs$ is obtained by AVL insertion of $x$ into the tree built from $xs$. Thus the list is
inserted from right to left, starting from the empty tree.
