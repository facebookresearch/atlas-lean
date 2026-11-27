# One augmentation step

Let $\mu$ be a partner array on a bipartite graph with $a$ left
vertices and $b$ right vertices. Run the alternating search from the unmatched left vertices for
$a + 1$ rounds and take the first right vertex $j$, in the order $0, \dots, b - 1$, that is
unmatched and reached. If there is none, the step fails. Otherwise it returns the partner array
obtained from $\mu$ by flipping the path found by walking back from $j$ through the search
layers: every right vertex $j'$ on the path gets as partner the left vertex paired with it on the
path, and every other right vertex keeps its partner.
