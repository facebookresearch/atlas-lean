# Approximation: forward-model error controls posterior error in Hellinger distance

Let the unknown $u$ live in a finite-dimensional real normed space with its Borel σ-algebra and prior probability measure $\mu_0$.
Let $\Phi$ be continuous and $\Phi^N$ measurable potentials with

$$
\Phi(u), \Phi^N(u) \ge -M_1(\|u\|), \qquad |\Phi(u) - \Phi^N(u)| \le M_2(\|u\|) \, \psi(N), \qquad \psi(N) \to 0,
$$

where $M_1$, $M_2$ are nondecreasing and independent of $N$ and $\exp(M_1(\|u\|))(1 + M_2(\|u\|)^2)$ is
integrable. Then there is $C$ such that, for all sufficiently large $N$,

$$
d_{\mathrm{Hell}}(\mu, \mu^N) \le C \, |\psi(N)| .
$$

Typically $\Phi^N$ is the misfit of a discretised forward model $G^N$, and the theorem says that the
posterior inherits the convergence rate of the forward solver.

This is Theorem 4.9 of Dashti and Stuart with $X' = X$ finite-dimensional (Assumptions 4.7).

## Sources

- Masoumeh Dashti and Andrew M. Stuart, *The Bayesian approach to inverse problems*, in *Handbook of Uncertainty Quantification*, Springer (2017), 311–428, DOI 10.1007/978-3-319-12385-1_7; numbering of arXiv:1302.6989v4 (2015), Assumptions 4.7, Theorems 4.8 and 4.9.
