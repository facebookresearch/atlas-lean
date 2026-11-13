# Dimension bounds for Lüroth well approximable sets via denominators

Let $\psi$ be a
function from the natural numbers to $(0, 1]$. Let $L(\psi)$ be the set of $x \in (0, 1]$ such
that $|x - P_n(x)/Q_n(x)| < \psi(Q_n(x))/Q_n(x)$ for infinitely many $n$, where $P_n(x)/Q_n(x)$
is the $n$-th Lüroth convergent of $x$ and $Q_n(x)$ its Lüroth denominator. For $k \ge 0$ let
$S_k$ be the set of numbers $d_k \prod_{j < k} d_j (d_j - 1)$, where $d_0, \ldots, d_k$ are
integers at least $2$ (the $k$-th Lüroth denominators, indexed from $0$). For $q \ge 2$ put
$r(q) = -\log \psi(q) / \log q$, and let
$\lambda_\psi = \liminf_{k \to \infty} \liminf_{q \in S_k, q \to \infty} r(q)$,
$\bar\lambda_\psi = \liminf_{k \to \infty} \limsup_{q \in S_k, q \to \infty} r(q)$,
$\tau_\psi = \liminf_{q \to \infty} r(q)$ and $\bar\tau_\psi = \limsup_{q \to \infty} r(q)$,
all taken in $[0, \infty]$. Then $\tau_\psi \le \lambda_\psi$, $\bar\lambda_\psi \le \bar\tau_\psi$
and $1/(1 + \bar\lambda_\psi) \le \dim_H L(\psi) \le 1/(1 + \lambda_\psi)$, where $1/\infty = 0$.

Since $S_k$ is indexed from $0$, it is the paper's $S_{k+1}$; this does not change the outer
limit inferior.

## Sources

- Ying Wai Lee, *Lüroth Expansions in Diophantine Approximation: Metric Properties and Conjectures*, INTEGERS 26 (2026), Article A45, Theorem 8.
