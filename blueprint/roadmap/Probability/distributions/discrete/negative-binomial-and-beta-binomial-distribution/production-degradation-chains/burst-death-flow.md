# Net probability flow of the bursty production–degradation chain

For real $\kappa, \gamma, b$, a function $p : \mathbb{N} \to \mathbb{R}$ and $n \in \mathbb{N}$, the net
probability flow into state $n$ is

$$\Phi(p)(n) = \kappa \sum_{m < n} p(m)\, \frac{b^{n - m}}{(1 + b)^{n - m + 1}} + \gamma (n + 1)\, p(n + 1) - \Bigl( \kappa \frac{b}{1 + b} + \gamma n \Bigr) p(n) .$$

For $\kappa, \gamma > 0$ and $b \ge 0$ this is the flow of the chain in which bursts arrive at rate
$\kappa$ and add $B$ molecules, $B$ geometric with mean $b$, $P(B = j) = b^j/(1 + b)^{j+1}$ for
$j \ge 0$, and each molecule decays at rate $\gamma$. A burst of size $0$ changes nothing, so state
$n$ is left by a burst at rate $\kappa P(B \ge 1) = \kappa b/(1 + b)$; a law $p$ is stationary
exactly when $\Phi(p)(n) = 0$ for every $n$.
