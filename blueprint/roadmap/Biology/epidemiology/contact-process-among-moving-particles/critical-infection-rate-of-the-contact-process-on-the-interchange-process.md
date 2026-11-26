# Critical infection rate of the contact process on the interchange process

**Model.** On $\mathbb{Z}^d$ each vertex is empty, occupied by a healthy particle, or occupied by an infected particle. Infected particles recover at rate $1$; an infected particle infects a healthy particle at each neighboring vertex at rate $\lambda > 0$; and, independently, the states of every pair of adjacent vertices are swapped at rate $\mathsf{v} > 0$ (the interchange process), so particles move and carry the infection with them. Start from a single infected particle at the origin, with every other vertex independently occupied by a healthy particle with probability $p \in (0,1]$ and empty otherwise. Let
$$\lambda_c(\mathsf{v}, p) = \inf\{\lambda > 0 : \text{the infection survives forever with positive probability}\}.$$

**Theorem.** For every $d \ge 1$ and every $p \in (0,1]$,
$$\lim_{\mathsf{v} \to \infty} \lambda_c(\mathsf{v}, p) = \frac{1}{2dp}.$$

## Expansion

As the swap rate grows, the environment seen by an infected particle is re-randomized between successive infection attempts, so the configuration around it looks like fresh Bernoulli($p$) product measure. Each infected particle then makes infection attempts at total rate $2d\lambda$, a fraction $p$ of which hit a healthy particle, while it recovers at rate $1$. The infected population therefore behaves like a branching process with mean offspring $2dp\lambda$, which is supercritical exactly when $\lambda > 1/(2dp)$. The proof makes this mean-field picture rigorous with renormalization and comparison to oriented percolation, using random-walk meeting estimates and decorrelation bounds for the interchange flow; the delicate direction is the upper bound in $d = 1, 2$, where two moving particles meet often.

## Sources

- M. Hilário, D. Ungaretti, D. Valesin, M. E. Vares, "Contact process on interchange process", arXiv:2509.02747 (2025), Theorem 1.1, <https://doi.org/10.48550/arXiv.2509.02747>.
