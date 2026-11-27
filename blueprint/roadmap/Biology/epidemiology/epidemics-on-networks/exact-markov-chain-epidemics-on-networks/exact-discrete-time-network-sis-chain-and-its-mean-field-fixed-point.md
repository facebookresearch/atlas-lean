# Exact discrete-time network SIS chain and its mean-field fixed point

**Exact model.** Let $G$ be a connected graph on $n$ nodes with adjacency matrix $A$, neighbourhoods $N_i$ and largest eigenvalue $\lambda_{\max}(A)$. The state $\xi(t) \in \{0,1\}^n$ records which nodes are infected. Given $\xi(t) = X$, nodes update independently. A susceptible node with $m_i$ infected neighbours stays susceptible with probability $(1-\beta)^{m_i}$. An infected node becomes susceptible with probability $\delta(1-\beta)^{m_i}$ (it recovers and is not reinfected). This is a $2^n$-state Markov chain whose unique stationary law is the all-healthy state.

**Mean-field map.** Replacing the neighbours' indicators by their marginal probabilities gives the $n$-dimensional map $p(t+1) = \Phi(p(t))$,

$$\Phi_i(x) = (1-\delta)x_i + \bigl(1 - (1-\delta)x_i\bigr)\Bigl(1 - \prod_{j\in N_i}(1 - \beta x_j)\Bigr), \qquad x \in [0,1]^n .$$

**Theorem.**

1. (Linear upper bound.) The exact marginals satisfy $p_i(t+1) \le (1-\delta)p_i(t) + \beta\sum_{j\in N_i}p_j(t)$, and the mean-field map bounds survival of the chain: $\mathbb P(\xi(t) \ne \mathbf 0 \mid \xi(0) = X) \le 1 - \prod_{i\in \mathrm{supp}(X)}\bigl(1 - \Phi^t_i(\mathbf 1)\bigr)$.
2. (Fast extinction below threshold.) If $\beta\lambda_{\max}(A)/\delta < 1$, the mixing time of the exact chain, that is, its time to absorption in the all-healthy state, is $O(\log n)$.
3. (Endemic fixed point above threshold.) If $\beta\lambda_{\max}(A)/\delta > 1$, equivalently $\lambda_{\max}\bigl((1-\delta)I_n + \beta A\bigr) > 1$, the map $\Phi$ has a unique fixed point $x^* \ne 0$ in $[0,1]^n$, and $\Phi^t(p(0)) \to x^*$ for every $p(0) \ne 0$. The same holds for the continuous-time mean-field system.

## Expansion

Item 1 follows by bounding $1 - \prod_j(1-\beta\mathbb 1_{\xi_j=1}) \le \beta\sum_j \mathbb 1_{\xi_j = 1}$ and taking expectations. Iterating the linear bound gives $\mathbb P(\xi(t) \ne 0) \le \sum_i p_i(t) \le \sqrt n\,\|(1-\delta)I + \beta A\|^t$, which is small once $t \gtrsim \log n/\log(1/(1-\delta+\beta\lambda_{\max}))$; this proves item 2. For item 3, write a fixed point as $\Psi_i(x) = \Xi_i(x) - \omega(x_i) = 0$ with $\Xi_i$ concave and increasing in the neighbours' coordinates. Concavity and the instability of the origin when $\lambda_{\max}((1-\delta)I + \beta A) > 1$ give existence and uniqueness of a positive zero. Monotonicity of $\Phi$ then gives global convergence by sandwiching iterates between iterates from $\mathbf 1$ and from a small positive vector.

## Sources

- Hyoung Jun Ahn, Babak Hassibi, "Global dynamics of epidemic spread over complex networks", 52nd IEEE Conference on Decision and Control (CDC 2013), 4579–4585, <https://doi.org/10.1109/CDC.2013.6760600>: the linear upper bound of item 1 and item 3.
- Hyoung Jun Ahn, Babak Hassibi, "On the mixing time of the SIS Markov chain model for epidemic spread", 53rd IEEE Conference on Decision and Control (CDC 2014), 6221–6227, <https://doi.org/10.1109/CDC.2014.7040364>: the survival bound of item 1 and the $O(\log n)$ mixing time of item 2.
- The two papers are combined in Navid Azizan Ruhi, Hyoung Jun Ahn, Babak Hassibi, "Analysis of Exact and Approximated Epidemic Models over Complex Networks", arXiv:1609.09565 (2016), Section 2: Theorems 2.3, 2.4 and 2.6 and Propositions 2.5 and 2.10, <https://doi.org/10.48550/arXiv.1609.09565>; theorem numbers refer to this version.
