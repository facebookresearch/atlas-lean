# The stopped discounted process freezes at the first entrance into $A$

Let $S$ be a set, $q : S \to \mathbb{R}$, $V : S \to [0, \infty]$, $c \in \mathbb{R}$ and
$A \subseteq S$, and let $D_n$ be the [stopped discounted process](discounted-stop.md). Let
$k \le n$ be natural numbers, $x \in S$ and $\omega$ a step sequence, with
[jump chain](../../../Probability/markov-chains/finite-continuous-time-markov-chains/finite-continuous-time-markov-chains-as-path-pro/ctmc-jump-chain.md)
$Y_j = Y_j(x, \omega)$ and [jump times](jump-time.md) $T_j = T_j(x, \omega)$. If $Y_j \notin A$ for
every $j < k$ and $Y_k \in A$, so that $k$ is the first entrance time into $A$, then

$$D_n(x, \omega) = e^{-c T_k}\, V(Y_k):$$

from the first entrance on, the process keeps its value at that entrance. No condition on $q$ or $c$
is needed.
