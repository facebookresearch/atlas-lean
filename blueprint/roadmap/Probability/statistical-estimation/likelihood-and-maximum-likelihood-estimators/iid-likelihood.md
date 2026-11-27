# Likelihood of an iid sample

Let $F$ be a normalized density family on $\Omega$ with
parameter set $\Theta$ and densities $f_\theta$ for $\theta \in \Theta$. For a sample size $n$,
a parameter $\theta \in \Theta$ and a sample $x = (x_0, \dots, x_{n-1}) \in \Omega^n$, the iid
likelihood of $\theta$ at $x$ is $L_n(\theta; x) = \prod_{i < n} f_\theta(x_i)$, a value in
$[0, \infty]$. For $n = 0$ this is the empty product $1$.
