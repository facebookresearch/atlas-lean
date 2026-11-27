# Steady-state moments and promoter-occupancy bounds of a self-regulating gene

Consider a gene whose promoter is either unbound ($U$) or bound by one of its own protein molecules ($B$), with mass-action reactions

$$U \xrightarrow{\lambda} U + P, \quad B \xrightarrow{\tilde\lambda} B + P, \quad U + P \xrightarrow{\psi} B, \quad B \xrightarrow{\theta} U + P, \quad P \xrightarrow{\mu} \emptyset,$$

with $\lambda, \psi, \theta, \mu > 0$ and $\tilde\lambda \ge 0$ ($\lambda > \tilde\lambda$ is negative feedback, $\lambda < \tilde\lambda$ positive feedback). Let $N$ be the total protein number (free plus bound) and $A = 1$ if the promoter is unbound, $A = 0$ if bound, in the unique steady state $X = (N, A)$.

1. **Flux balance.** For $n \ge 1$, $\mu n\,\mathbb{P}(X=(n,1)) + \mu(n-1)\,\mathbb{P}(X=(n,0)) = \lambda\,\mathbb{P}(X=(n-1,1)) + \tilde\lambda\,\mathbb{P}(X=(n-1,0))$, and promoter switching balances: $\theta\,\mathbb{P}(A=0) = \psi\,\mathbb{E}[N\mathbf{1}_{A=1}]$.
2. **First moments.**

$$\mathbb{E}[N] = \mathbb{P}(A=0)\Bigl(1 + \frac{\tilde\lambda}{\mu}\Bigr) + \mathbb{P}(A=1)\frac{\lambda}{\mu}, \qquad \mathbb{E}[N\mathbf{1}_{A=1}] = \mathbb{P}(A=0)\frac{\theta}{\psi},$$

so that $\min(\lambda, \tilde\lambda + \mu)/\mu \le \mathbb{E}[N] \le \max(\lambda, \tilde\lambda+\mu)/\mu$.
3. **Promoter occupancy.** If $\tilde\lambda = \lambda$, the protein number is Poisson in both states and $\mathbb{P}(A=1) = \mu\theta/(\mu\theta + \lambda\psi)$. In general

$$\frac{\mu\theta}{\mu\theta + \max(\lambda,\tilde\lambda)\,\psi} \le \mathbb{P}(A=1) \le \frac{\mu\theta}{\mu\theta + \min(\lambda,\tilde\lambda)\,\psi} .$$

All higher moments of $N$ and $N\mathbf{1}_{A=1}$ are affine functions of $\mathbb{P}(A=1)$, given by explicit recursions in the moment order.

## Expansion

The balance identities equate the probability flux across the cut between $n-1$ and $n$ proteins and between the two promoter states. Summing them with weights $1$ and $n$ gives the first moments. The occupancy bounds follow by comparing the protein count in each promoter state with Poisson laws with means $\lambda/\mu$ and $\tilde\lambda/\mu$. Note that one protein is always bound in state $B$, which accounts for the $1$ in the first-moment formula.

## Sources

- Martin Jansen, "Stochastic equations for a self-regulating gene", International Journal of Biomathematics 10 (2017), 1750046, <https://doi.org/10.1142/s1793524517500462>; numbering as in arXiv:1403.3265: Theorem 1, Corollary 2.1, Corollary 2.3 and Theorem 3.
