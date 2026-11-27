# Net probability flow of the immigration–death chain

For real $\kappa, \gamma$ and $p : \mathbb{N} \to \mathbb{R}$, the net probability flow of the
immigration–death chain is

$$\Phi(p)(0) = \gamma\, p(1) - \kappa\, p(0), \qquad \Phi(p)(n) = \kappa\, p(n - 1) + \gamma (n + 1)\, p(n + 1) - (\kappa + \gamma n)\, p(n) \quad (n \ge 1) .$$

It is the flow into state $n$ of the chain on $\mathbb{N}$ in which molecules are made at rate
$\kappa$ ($n \to n + 1$) and each decays at rate $\gamma$ ($n \to n - 1$ at rate $\gamma n$); a law $p$
is stationary (global balance) exactly when $\Phi(p)(n) = 0$ for every $n$.
