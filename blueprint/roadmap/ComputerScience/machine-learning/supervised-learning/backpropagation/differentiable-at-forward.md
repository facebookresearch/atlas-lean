# Differentiability of the forward pass

Let $N$ be a feedforward network with layers
$f_k : \mathbb{R}^{d_k} \to \mathbb{R}^{d_{k+1}}$ between Euclidean spaces, let
$x \in \mathbb{R}^{d_0}$ and $n \in \mathbb{N}$, and write
$N_j : \mathbb{R}^{d_0} \to \mathbb{R}^{d_j}$ for the forward pass through the first $j$ layers. If
$f_j$ is differentiable at $N_j(x)$ for every $j < n$, then $N_n$ is differentiable at $x$.
