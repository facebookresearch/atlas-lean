# The amortized cost of a move-to-front step

Let $M$ be a list of distinct items, $L$ a
rearrangement of $M$ (the offline list), and $x$ an item of $M$ at position $k$ in $M$ and
position $i$ in $L$, counting from $1$. Let $\Phi$ be the number of inversions between $M$ and
$L$ (the pairs of items that the two lists order differently), and $\Phi'$ the number of
inversions between the list obtained from $M$ by moving $x$ to the front and $L$. Then
$k + \Phi' \le \Phi + 2i - 1$.

This is the amortized step of Sleator and Tarjan's analysis, with potential $\Phi$.
