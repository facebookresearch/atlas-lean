# The network at fixed parameters

Let $P$ be a network with parameters whose layer $k$ is a
map $g_k : \mathbb{R}^{p_k} \times \mathbb{R}^{d_k} \to \mathbb{R}^{d_{k+1}}$ of the parameters
and the input (all spaces Euclidean). For parameters $\theta = (\theta_k)_{k \in \mathbb{N}}$ with
$\theta_k \in \mathbb{R}^{p_k}$, the network at $\theta$ is the feedforward network whose layer
$k$ is $g_k(\theta_k, \cdot) : \mathbb{R}^{d_k} \to \mathbb{R}^{d_{k+1}}$.
