# With fewer observations than parameters, $A$ is not identifiable

For natural numbers $m < n$ and every real $m \times n$ matrix $A$, the calibration model
$y = A\theta$ is not [identifiable](identifiable.md): the linear map
$\theta \mapsto A\theta$ from $\mathbb{R}^n$ to $\mathbb{R}^m$ is not injective. By the
rank–nullity theorem its kernel has dimension at least $n - m > 0$, so it contains a nonzero
vector, and that vector and $0$ have the same image.
