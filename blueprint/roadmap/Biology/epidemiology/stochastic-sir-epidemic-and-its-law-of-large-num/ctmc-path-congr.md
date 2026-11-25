# Paths with the same jump chain and jump times agree

Let $Q$ be a real square matrix indexed by a set $\iota$ and $i \in \iota$, and let $\omega$ and
$\omega'$ be two step sequences $((\xi_n, E_n))_{n \in \mathbb{N}}$, with $\xi_n : \iota \to \iota$
and $E_n \in \mathbb{R}$. If they have the same
[jump chain](../../../Probability/markov-chains/finite-continuous-time-markov-chains/finite-continuous-time-markov-chains-as-path-pro/ctmc-jump-chain.md)
from $i$, $Y_n(i, \omega) = Y_n(i, \omega')$ for every $n$, and the same
[jump times](../../../Probability/markov-chains/finite-continuous-time-markov-chains/finite-continuous-time-markov-chains-as-path-pro/ctmc-jump-time.md)
for $Q$, $T_n(i, \omega) = T_n(i, \omega')$ for every $n$, then their
[paths](../../../Probability/markov-chains/finite-continuous-time-markov-chains/finite-continuous-time-markov-chains-as-path-pro/ctmc-path.md)
agree: $X_t(i, \omega) = X_t(i, \omega')$ for every $t \ge 0$. So the path depends on the steps only
through the jump chain and the jump times.
