# Exact success probability of Grover search

Let $\alpha$ be a finite search space and
$M \subseteq \alpha$ a marked set such that both $M$ and its complement are nonempty, and let
$\theta = \arcsin \sqrt{|M| / |\alpha|}$ be the Grover angle of $M$. For $k \in \mathbb{N}$, let
$\psi_k$ be the vector obtained by applying the Grover step for $M$ $k$ times to the uniform
amplitude vector, whose value is $1/\sqrt{|\alpha|}$ at every point. Then the marked probability
of $\psi_k$ is $\sum_{x \in M} \psi_k(x)^2 = \sin^2((2k + 1)\theta)$.
