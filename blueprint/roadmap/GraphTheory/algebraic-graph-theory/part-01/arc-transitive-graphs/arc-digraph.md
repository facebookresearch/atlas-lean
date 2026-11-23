# $s$-arc digraph

Let $X$ be a finite graph and $s$ a natural number. For an
$(s+1)$-arc $\gamma = (x_0, \dots, x_{s+1})$ of $X$, its *head* is the $s$-arc
$(x_1, \dots, x_{s+1})$ and its *tail* is the $s$-arc $(x_0, \dots, x_s)$. If $\alpha$ and
$\beta$ are $s$-arcs of $X$, then $\beta$ *follows* $\alpha$ if there is an $(s+1)$-arc of $X$
whose tail is $\alpha$ and whose head is $\beta$. The *$s$-arc digraph* $X^{(s)}$ is the directed
graph whose vertices are the $s$-arcs of $X$, with an arc from $\alpha$ to $\beta$ if and only if
$\beta$ follows $\alpha$.
