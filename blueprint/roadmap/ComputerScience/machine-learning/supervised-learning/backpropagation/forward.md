# The forward pass

For a feedforward network with layers
$f_k : \mathbb{R}^{d_k} \to \mathbb{R}^{d_{k+1}}$ between Euclidean spaces, the forward pass
through the first $n$ layers is the map $N_n : \mathbb{R}^{d_0} \to \mathbb{R}^{d_n}$ given by
$N_0(x) = x$ and $N_{n+1}(x) = f_n(N_n(x))$, that is, $N_n = f_{n-1} \circ \cdots \circ f_0$.
