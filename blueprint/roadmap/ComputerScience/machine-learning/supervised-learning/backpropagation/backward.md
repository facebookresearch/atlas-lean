# The backward pass

Let $N$ be a feedforward network with layers
$f_k : \mathbb{R}^{d_k} \to \mathbb{R}^{d_{k+1}}$ between Euclidean spaces, let
$x \in \mathbb{R}^{d_0}$ be an input, and write $a_k \in \mathbb{R}^{d_k}$ for the forward pass of
$x$ through the first $k$ layers. For each $n \in \mathbb{N}$, the backward pass at $x$ sends a
vector $\delta \in \mathbb{R}^{d_n}$ to $B_n(\delta) \in \mathbb{R}^{d_0}$, defined by
$B_0(\delta) = \delta$ and $B_{n+1}(\delta) = B_n(Df_n(a_n)^* \, \delta)$, where $Df_n(a_n)$ is the
Fréchet derivative of $f_n$ at $a_n$ (taken to be $0$ if $f_n$ is not differentiable there) and
$^*$ denotes the adjoint. Thus
$B_n(\delta) = Df_0(a_0)^* \cdots Df_{n-1}(a_{n-1})^* \, \delta$: the adjoints of the layer
Jacobians are applied from the last layer to the first.
