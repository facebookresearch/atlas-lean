# Expected supremum of a Gaussian process

Let $n \in \mathbb{N}$ and let $T \subset \mathbb{R}^n$ be a finite nonempty set. The Gaussian supremum of $T$ is

$$g(T) = \int_{\mathbb{R}^n} \max_{t \in T} \langle t, x \rangle \, d\gamma_n(x) = \mathbb{E}_x \max_{t \in T} \sum_{i=1}^n t_i x_i,$$

where $\gamma_n$ is the standard Gaussian measure on $\mathbb{R}^n$, the product of $n$ copies of $\mathcal{N}(0, 1)$. Nonemptiness of $T$ is required so that the maximum is defined.
