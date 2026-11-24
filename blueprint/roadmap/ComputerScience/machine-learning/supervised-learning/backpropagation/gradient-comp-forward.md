# Backpropagation computes the input gradient

Let $N$ be a feedforward network with layers
$f_k : \mathbb{R}^{d_k} \to \mathbb{R}^{d_{k+1}}$ between Euclidean spaces, let
$x \in \mathbb{R}^{d_0}$ and $n \in \mathbb{N}$, and write $N_j$ for the forward pass through the
first $j$ layers. Assume that $f_j$ is differentiable at $N_j(x)$ for every $j < n$, and let
$\ell : \mathbb{R}^{d_n} \to \mathbb{R}$ be differentiable at $N_n(x)$. Then
$\nabla(\ell \circ N_n)(x)$ is the backward pass of $\nabla \ell(N_n(x))$ at input $x$ through
the first $n$ layers, that is,
$\nabla(\ell \circ N_n)(x) = Df_0(N_0(x))^* \cdots Df_{n-1}(N_{n-1}(x))^* \, \nabla \ell(N_n(x))$,
where $Df_j(N_j(x))$ is the Fréchet derivative of $f_j$ at $N_j(x)$ and $^*$ denotes the
adjoint.
