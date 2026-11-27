# Maximum likelihood estimator

Let $F$ be a normalized density family on $\Omega$ with
parameter set $\Theta$, let $n$ be a sample size, and let $L_n(\theta; x)$ denote the iid
likelihood of $\theta \in \Theta$ at a sample $x \in \Omega^n$. A map $\hat\theta$ from
$\Omega^n$ to $\Theta$ is a maximum likelihood estimator for samples of size $n$ if for every
sample $x \in \Omega^n$ the parameter $\hat\theta(x)$ maximizes $\theta \mapsto L_n(\theta; x)$
over all of $\Theta$.
