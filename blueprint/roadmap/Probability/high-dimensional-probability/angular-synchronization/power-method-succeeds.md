# Success of the projected power method

For a matrix $C \in \mathbb{C}^{n \times n}$, the projected power method succeeds on $C$ if there is $\hat{x} \in \mathbb{C}^n$ such that

1. $\hat{x}$ is a global maximizer of $\operatorname{Re}(x^* C x)$ over $\{x \in \mathbb{C}^n : \lvert x_k \rvert = 1 \text{ for all } k\}$, unique up to a global phase (every maximizer equals $e^{i\theta} \hat{x}$ for some $\theta \in \mathbb{R}$); and
2. for every scaled leading eigenvector $x_0$ of $C$ (a maximizer of $\operatorname{Re}(y^* C y)$ over $\lVert y \rVert_2^2 = n$), there are phases $\theta_t \in \mathbb{R}$ with $e^{i\theta_t} x_t \to \hat{x}$ as $t \to \infty$, where $x_{t+1} = P(C x_t)$ are the projected power iterates, $P(a)_k = a_k / \lvert a_k \rvert$ for $a_k \neq 0$ and $P(a)_k = 1$ for $a_k = 0$.
