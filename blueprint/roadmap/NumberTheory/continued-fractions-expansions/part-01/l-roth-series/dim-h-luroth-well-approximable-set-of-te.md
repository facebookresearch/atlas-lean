# Dimension of Lüroth well approximable sets under a divergence condition

Let $\psi$ be a
function from the natural numbers to $(0, 1]$. Let $L(\psi)$ be the set of $x \in (0, 1]$ such
that $|x - P_n(x)/Q_n(x)| < \psi(Q_n(x))/Q_n(x)$ for infinitely many $n$, where $P_n(x)/Q_n(x)$
is the $n$-th Lüroth convergent of $x$ and $Q_n(x)$ its Lüroth denominator. Let
$\tau_\psi = \liminf_{q \to \infty} (-\log \psi(q) / \log q)$, taken in $[0, \infty]$, be the
lower order at infinity of $1/\psi$, and suppose $\tau_\psi > 1$. Put $t = 1/(1 + \tau_\psi)$,
with $t = 0$ if $\tau_\psi = \infty$, and $\theta_t(q) = \min\{1, 2^{-t} q^{1-t} \psi(q)^t\}$.
Suppose that $\theta_t$ is non-increasing on $\{q : q \ge 1\}$ and that the partial sums
$\sum_{q=1}^{N} -(\psi(q)/q)^t ((1 - t) \log q + t \log(\psi(q)/2))$ tend to $+\infty$ as
$N \to \infty$. Then the Hausdorff dimension of $L(\psi)$ is $1/(1 + \tau_\psi)$, read as $0$
when $\tau_\psi = \infty$.

The paper's monotonicity of $\theta_t$ on $\mathbb{N}$ is taken on $q \ge 1$ (at $q = 0$ the
formula gives $0$). The terms of the series need not be nonnegative, so its divergence to
$\infty$ is read as the partial sums tending to $+\infty$.

## Sources

- Ying Wai Lee, *Lüroth Expansions in Diophantine Approximation: Metric Properties and Conjectures*, INTEGERS 26 (2026), Article A45, Theorem 10.
