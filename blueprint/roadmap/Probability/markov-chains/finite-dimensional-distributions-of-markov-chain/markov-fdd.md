# Finite-dimensional distribution of a Markov chain

For a measure $\mu$ on a measurable
space $S$, a kernel $\kappa$ from $S$ to $S$, a natural number $n$ and sets
$A_0, \dots, A_n \subseteq S$, the finite-dimensional distribution
$\mathrm{FDD}_n(\mu, \kappa; A_0, \dots, A_n) \in [0, \infty]$ is defined by recursion on $n$:
$\mathrm{FDD}_0(\mu, \kappa; A_0) = \mu(A_0)$ and
$\mathrm{FDD}_{n+1}(\mu, \kappa; A_0, \dots, A_{n+1}) =
\int_{A_0} \mathrm{FDD}_n(\kappa(x), \kappa; A_1, \dots, A_{n+1}) \, d\mu(x)$.
Unfolded, it is the iterated integral

$$
\int_{A_0} \mu(dx_0) \int_{A_1} \kappa(x_0, dx_1) \cdots \int_{A_n} \kappa(x_{n-1}, dx_n).
$$

When $\mu$ is a probability measure and $\kappa$ a Markov kernel, this is the probability that a
chain with initial distribution $\mu$ and transition kernel $\kappa$ visits $A_0, A_1, \dots, A_n$
at consecutive times.
