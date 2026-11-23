# Cached lower bound of a range tree

For a range tree $t$, $\operatorname{tmin}(t)$ is
$0$ if $t$ is empty, $x$ if $t$ is a single leaf with value $x$, and the stored lower bound
$lo$ if $t$ is a node with stored bounds $lo$, $hi$ and two subtrees.

The value $0$ for the empty tree is a sentinel without meaning. The value
$\operatorname{tmin}(t)$ is read from the root and does not depend on the subtrees.
