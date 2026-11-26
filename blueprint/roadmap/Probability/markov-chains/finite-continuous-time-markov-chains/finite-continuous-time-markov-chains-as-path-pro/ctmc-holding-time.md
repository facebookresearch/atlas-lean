# Holding times of a continuous-time Markov chain

Let $Q$ be a real square matrix indexed by a set $S$, with exit rates $q(k) = -Q(k, k)$, let
$\omega = ((\xi_n, E_n))_{n \in \mathbb{N}}$ be a step sequence and $Y_n = Y_n(i, \omega)$ the [jump
chain](ctmc-jump-chain.md) started at $i$. The $n$-th holding time is the element of $[0, \infty]$

$$S_n = \begin{cases} \infty & \text{if } q(Y_n) = 0, \\ \max\bigl(E_n / q(Y_n), 0\bigr) & \text{otherwise.} \end{cases}$$

It is infinite exactly when $q(Y_n) = 0$, which for a rate matrix means that $Y_n$ is absorbing.
When $q(Y_n) > 0$, a negative clock value $E_n$ gives $S_n = 0$; under the step law of a rate matrix
the clocks are exponential, so this is a null event. (When $q(Y_n) < 0$, which a rate matrix
excludes, a negative clock gives a positive time.)
