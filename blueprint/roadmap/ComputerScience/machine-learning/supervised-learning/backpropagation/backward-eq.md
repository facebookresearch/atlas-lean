# The backward pass is the vector-Jacobian product

Let $N$ be a feedforward network with
layers $f_k : \mathbb{R}^{d_k} \to \mathbb{R}^{d_{k+1}}$ between Euclidean spaces, let
$x \in \mathbb{R}^{d_0}$ and $n \in \mathbb{N}$, and write
$N_j : \mathbb{R}^{d_0} \to \mathbb{R}^{d_j}$ for the forward pass through the first $j$ layers. If
$f_j$ is differentiable at $N_j(x)$ for every $j < n$, then for every $\delta \in \mathbb{R}^{d_n}$
the backward pass from $\delta$ at input $x$ through the first $n$ layers equals
$DN_n(x)^* \, \delta$, where $DN_n(x)$ is the Fréchet derivative of $N_n$ at $x$ and $^*$ denotes
the adjoint.
