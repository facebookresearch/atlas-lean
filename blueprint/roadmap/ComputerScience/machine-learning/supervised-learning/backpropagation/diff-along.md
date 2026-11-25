# Differentiability along the forward pass

Let $N$ be a feedforward network with layers
$f_k : \mathbb{R}^{d_k} \to \mathbb{R}^{d_{k+1}}$ between Euclidean spaces, let
$x \in \mathbb{R}^{d_0}$ and $n \in \mathbb{N}$, and write $a_j \in \mathbb{R}^{d_j}$ for the
forward pass of $x$ through the first $j$ layers. The network is differentiable along the forward
pass of $x$ through its first $n$ layers when $f_j$ is differentiable at $a_j$ for every
$j < n$.
