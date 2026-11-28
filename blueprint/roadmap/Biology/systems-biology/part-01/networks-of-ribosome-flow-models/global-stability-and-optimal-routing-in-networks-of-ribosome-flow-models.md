# Global stability and optimal routing in networks of ribosome flow models

**Building block.** The ribosome flow model with input and output (RFMIO) of length $n$ with rates $\lambda_0, \dots, \lambda_n > 0$ and input $u(t) > 0$ is

$$\dot x_1 = u\lambda_0(1 - x_1) - \lambda_1 x_1 (1 - x_2), \qquad \dot x_i = \lambda_{i-1} x_{i-1}(1 - x_i) - \lambda_i x_i (1 - x_{i+1}) \ (2 \le i \le n-1),$$

$$\dot x_n = \lambda_{n-1} x_{n-1}(1 - x_n) - \lambda_n x_n, \qquad y = \lambda_n x_n,$$

with occupancies $x_i \in [0,1]$; $y$ is the ribosome exit (protein production) rate. For constant $u \equiv c$ it is an RFM with initiation rate $c\lambda_0$, whose steady state is given spectrally: if $\sigma > 0$ and $\zeta > 0$ are the Perron eigenvalue and eigenvector of the symmetric tridiagonal $(n+2)\times(n+2)$ matrix with zero diagonal and off-diagonal entries $(c\lambda_0)^{-1/2}, \lambda_1^{-1/2}, \dots, \lambda_n^{-1/2}$, then $y_{ss} = \sigma^{-2}$ and $e_i = \lambda_i^{-1/2}\sigma^{-1}\zeta_{i+2}/\zeta_{i+1}$.

**Network.** Take $m$ RFMIOs, RFMIO $j$ with dimension $n_j$, input $u_j$ and output $y_j$, and a source of rate $y_0 > 0$. With weights $v_{k,j} \in [0,1]$ ($k \in \{0, \dots, m\}$, $j \in \{1, \dots, m+1\}$) set

$$u_j = \sum_{k=0}^m v_{k,j}\, y_k, \qquad y := y_{m+1} = \sum_{j=1}^m v_{j,m+1}\, y_j .$$

The network is **feasible** if every $v_{k,j} \in [0,1]$ and $\sum_{j=1}^{m+1} v_{k,j} = 1$ for each $k$ (each output is distributed, not created). Feedback loops (for example ribosome recycling from an output back to an input) are allowed. Let $z \in [0,1]^\ell$, $\ell = \sum_j n_j$, collect all occupancies.

**Theorem.**

1. *(Global asymptotic stability.)* A feasible network in which every RFMIO receives positive input at steady state (for example, each RFMIO is reachable from the source along positive weights) has a steady state $e \in (0,1)^\ell$ with $\lim_{t\to\infty} z(t,a) = e$ for every initial condition $a \in [0,1]^\ell$. The conclusion persists if $\sum_j v_{k,j} = 1$ is relaxed to $\sum_j v_{k,j} \le 1$.
2. *(Feed-forward computation.)* If the connection graph is acyclic, the steady state can be computed RFMIO by RFMIO from the spectral formula, each downstream RFMIO seeing the constant input $u_{ss}$. (The source states that $y_{ss}$ is then strictly concave in the weights; this fails already for two one-site RFMIOs in a feed-forward network, and holds for one split of a constant source among RFMIOs that feed the output directly.)
3. *(Optimal routing is convex.)* Maximizing $y_{ss}$ over feasible weights can be cast as a strictly convex optimization problem, so its optimum is unique, through a reparametrization of the inputs by the flows they carry (for example $u = y_0 + w$ with $0 \le w \le y$ for a feedback loop), since $y_{ss}$ need not be concave in the original weights, with or without feedback.

## Expansion

Each RFMIO is cooperative and contractive on the unit cube, and interconnecting contractive subsystems through distributing (sum-at-most-one) weights keeps the whole network contractive, which gives a unique globally attracting steady state for any wiring. Concavity in the flow variables comes from the concavity of the single-RFM production rate $\sigma^{-2}$ in the rates (it is positively homogeneous of degree one, hence not strictly concave, but strictly concave in the initiation rate alone); along a feed-forward cascade each output becomes the next RFMIO's initiation factor. In the one-site example $\dot x_1 = (1 - x_1)u - x_1$ with $u = 0.1 + v y$, the steady output is convex in $v$, but in the variable $w = vy$ it is the strictly concave $(0.1 + w)/(1.1 + w)$ on a convex feasible set; the optimum $v^* = 1$ gives $y_{ss}^* = 0.2702$. Splitting a common ribosome pool between two transcripts puts more of the pool on the faster mRNA. In the yeast example (a heterologous GFP gene and an endogenous gene) the optimal share is $v^* = 0.4311$.

## Sources

- I. Nanikashvili, Y. Zarai, A. Ovseevich, T. Tuller, M. Margaliot, "Networks of ribosome flow models for modeling and analyzing intracellular traffic", Scientific Reports 9 (2019) 1703, Eqs. (1)–(6), Theorem 1, Theorem 2, Proposition 1 (with Example 3), Proposition 2, Theorem 3, Example 6, <https://doi.org/10.1038/s41598-018-37864-1>, PMCID: PMC6368613.
