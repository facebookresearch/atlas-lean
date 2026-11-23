# Backpropagation computes the parameter gradients

Let $P$ be a network with parameters
whose layer $i$ is a map $g_i : \mathbb{R}^{p_i} \times \mathbb{R}^{d_i} \to \mathbb{R}^{d_{i+1}}$
of the parameters and the input (all spaces Euclidean). Fix parameters $\theta = (\theta_i)_i$
with $\theta_i \in \mathbb{R}^{p_i}$, let $N$ be the network with layers
$f_i = g_i(\theta_i, \cdot)$, let $x \in \mathbb{R}^{d_0}$ and $k, m \in \mathbb{N}$, set
$L = k + 1 + m$, and write $a_j$ for the forward pass of $x$ through the first $j$ layers of $N$.
Assume that $f_{k+1+i}$ is differentiable at $a_{k+1+i}$ for every $i < m$, that
$h(t) = g_k(t, a_k)$ is differentiable at $\theta_k$, and that
$\ell : \mathbb{R}^{d_L} \to \mathbb{R}$ is differentiable at $a_L$. For
$t \in \mathbb{R}^{p_k}$ let $\Phi(t)$ be the forward pass of $x$ through the first $L$ layers of
the network obtained by replacing $\theta_k$ with $t$. Then

$$\nabla(\ell \circ \Phi)(\theta_k) = Dh(\theta_k)^* \, \delta,$$

where $\delta = Df_{k+1}(a_{k+1})^* \cdots Df_{L-1}(a_{L-1})^* \, \nabla \ell(a_L)$ (so
$\delta = \nabla \ell(a_L)$ when $m = 0$) is the backward pass of $\nabla \ell(a_L)$ through
layers $k + 1, \dots, L - 1$ of $N$, $D$ denotes the Fréchet derivative and $^*$ the adjoint.
