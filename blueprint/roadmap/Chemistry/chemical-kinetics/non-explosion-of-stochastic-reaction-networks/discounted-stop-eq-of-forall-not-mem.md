# Before entering $A$, the stopped process equals $e^{-cT_n} V(Y_n)$

Let $S$ be a set, $q : S \to \mathbb{R}$, $V : S \to [0, \infty]$, $c \in \mathbb{R}$ and
$A \subseteq S$, and let $D_n$ be the [stopped discounted process](discounted-stop.md). Let
$n \in \mathbb{N}$, $x \in S$ and $\omega$ a step sequence, with
[jump chain](../../../Probability/markov-chains/finite-continuous-time-markov-chains/finite-continuous-time-markov-chains-as-path-pro/ctmc-jump-chain.md)
$Y_j = Y_j(x, \omega)$ and [jump times](jump-time.md) $T_j = T_j(x, \omega)$. If $Y_j \notin A$ for
every $j < n$, then

$$D_n(x, \omega) = e^{-c T_n}\, V(Y_n),$$

a product in $[0, \infty]$, whether or not $Y_n \in A$. No condition on $q$ or $c$ is needed.
