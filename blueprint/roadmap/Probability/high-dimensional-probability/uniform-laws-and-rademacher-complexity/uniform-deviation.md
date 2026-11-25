# Uniform deviation of empirical means

For a probability measure $P$ on $\mathcal{X}$, a class $\mathcal{F} = \{f_i : i \in I\}$ of
functions and a sample $x = (x_1, \dots, x_n)$ of size $n \ge 1$, the uniform deviation is

$$\|P_n - P\|_{\mathcal{F}} = \sup_{i \in I} \Big|\frac1n \sum_{k=1}^n f_i(x_k) - \mathbb{E}_P[f_i]\Big|.$$

Here $\mathbb{E}_P[f_i] = \int f_i \, dP$ is $0$ when $f_i$ is not integrable, and the supremum is taken to be $0$ when
it is infinite or $I$ is empty.

## Sources

- M. J. Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*, Cambridge University Press, 2019, §4.1.2 (uniform laws for more general function classes).
