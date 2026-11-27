# Extracting a compression collision from a Merkle–Damgård collision

Let
$h : S \times B \to S$ be a compression function, $iv \in S$ an initial value and
$\ell : \mathbb{N} \to B$ a length encoding. Let $M = (x_1, \dots, x_L)$ and
$M' = (x'_1, \dots, x'_{L'})$ be lists of blocks with chaining values $z_0 = z'_0 = iv$,
$z_i = h(z_{i-1}, x_i)$ and $z'_j = h(z'_{j-1}, x'_j)$. The procedure compares the final
compression inputs $(z_L, \ell(L))$ and $(z'_{L'}, \ell(L'))$ and returns this pair if they
differ. Otherwise, for $k = 1, 2, \dots, \min(L, L')$ in turn, it compares
$(z_{L-k}, x_{L-k+1})$ with $(z'_{L'-k}, x'_{L'-k+1})$ and returns the first such pair that
differs; if there is none, it returns no output.
