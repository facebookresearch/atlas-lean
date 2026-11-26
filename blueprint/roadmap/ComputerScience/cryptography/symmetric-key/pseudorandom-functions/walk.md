# Walking down the evaluation tree

Let $G : S \to S \times S$ and write
$G(s) = (G_0(s), G_1(s))$. For a list of bits $b_1, \dots, b_n$ and $t \in S$, the walk from $t$
along $b_1 \cdots b_n$ is $G_{b_n}(\cdots G_{b_2}(G_{b_1}(t)) \cdots)$: starting from a node of
the evaluation tree labelled $t$, each bit $b$ moves from the current node, labelled $s$, to its
child labelled $G_b(s)$ (the left child for $b = 0$, the right child for $b = 1$). The walk along
the empty list is $t$.
