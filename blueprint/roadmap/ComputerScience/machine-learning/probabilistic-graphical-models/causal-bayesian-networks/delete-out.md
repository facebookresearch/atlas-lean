# The graph $G_{\underline Z}$

**The graph $G_{\underline Z}$** (Pearl 1995, §4.2): let $B$ be a Bayesian network on the nodes
$0, \dots, n - 1$ with values in a type $\alpha$, let $Z$ be a finite set of nodes and
$z \in \alpha^n$ an assignment. The network $B_{\underline Z}$ is $B$ with every arrow leaving a
node of $Z$ removed: each node keeps only its parents outside $Z$, and its table is the table of
$B$ with every dropped parent $i \in Z$ read at the value $z_i$. Only the graph of this network
enters the do-calculus.
