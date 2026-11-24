# Where $\delta^\ast$ can attain its maximum

Let $L$ and $\tilde L$ be lists of natural
numbers forming a periodic Zeckendorf pair, let $N$ be the length of $L$, let $E^*$ and
$\tilde E^*$ be the collections determined by $L$ and $\tilde L$, let $\bar E^*$ be the closure
of $E^*$, and let $Q$ and $\tilde Q$ be fundamental sequences of $E^*$ and $\tilde E^*$. Let
$\delta^*$ be the function $\delta^*$ of $L$, $\tilde L$, $Q$, $\tilde Q$, and let $p$ be the
generic exponent of $Q$ and $\tilde Q$. Indices start at $0$: put $\omega = Q_0$ and
$\tilde\omega = \tilde Q_0$, write $\sum \varepsilon \tilde Q = \sum_k \varepsilon_k \tilde Q_k$
for a coefficient function $\varepsilon : \mathbb N \to \mathbb N$, and for $s \in \mathbb N$ let
$\bar\beta_s$ be the maximal $L^*$-block starting at index $s$. First, if $y \in (0, 1)$ and
$\delta^*(x) \le \delta^*(y)$ for all $x \in (0, 1)$, then $y = \sum \varepsilon \tilde Q$ for
some $\varepsilon \in \bar E^*$ with $\varepsilon \notin E^*$. Second, let $\ell \ge 1$ be a
natural number and let $\eta : \mathbb N \to \mathbb N$ be a sum of disjoint proper $L^*$-blocks
(possibly none) whose support intervals $[s, k]$ all satisfy $k < \ell - 1$. If
$\delta^*(x) \le \delta^*\bigl(\sum (\eta + \bar\beta_{\ell - 1}) \tilde Q\bigr)$ for all
$x \in (0, 1)$, then

$$
\ell < \max\left(2,\ p + 1 +
\frac{N \ln(1 / \omega) + \ln\left(1 - \sum \bar\beta_0 \tilde Q + \tilde\omega^N\right)}
{\ln(1 / \tilde\omega) - \ln(1 / \omega)}\right).
$$

In the source's one-based indexing $\bar\beta_s$ is $\bar\beta^{s+1}$, so the blocks
$\zeta^m$ of $\eta$ lie inside $[1, \ell - 1]$, the point is
$\sum (\sum_m \zeta^m + \bar\beta^\ell) \tilde Q$, and with $\varphi = 1 / \omega$,
$\tilde\varphi = 1 / \tilde\omega$ and $\rho = \sum \bar\beta^1 \tilde Q$ the right side is the
source's $\max\{2, p^*\}$.

## Sources

- Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25, Theorem 13.
