# Expected supremum of a Bernoulli process

Let $n \in \mathbb{N}$ and let $T \subset \mathbb{R}^n$ be a finite nonempty set. The Bernoulli supremum of $T$ is the expected maximum of the Bernoulli process indexed by $T$:

$$b(T) = \frac{1}{2^n} \sum_{x \in \{-1, 1\}^n} \max_{t \in T} \langle t, x \rangle = \mathbb{E}_x \max_{t \in T} \sum_{i=1}^n t_i x_i,$$

where $x$ is uniformly distributed on the $2^n$ sign vectors. Nonemptiness of $T$ is required so that the maximum is defined.
