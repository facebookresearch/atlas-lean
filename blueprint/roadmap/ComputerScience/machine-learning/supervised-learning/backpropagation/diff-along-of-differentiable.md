# Differentiable layers are differentiable along every forward pass

Let $N$ be a
feedforward network with layers $f_k : \mathbb{R}^{d_k} \to \mathbb{R}^{d_{k+1}}$ between
Euclidean spaces. If every $f_k$ is differentiable on all of $\mathbb{R}^{d_k}$, then for every
input $x \in \mathbb{R}^{d_0}$ and every $n \in \mathbb{N}$, the layer $f_j$ is differentiable at
the forward pass of $x$ through the first $j$ layers for every $j < n$.
