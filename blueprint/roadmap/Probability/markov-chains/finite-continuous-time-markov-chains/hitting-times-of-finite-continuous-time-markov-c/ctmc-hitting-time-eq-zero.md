# Hitting time from inside the target set is zero

Let $Q$ be a real square matrix indexed by a set $S$, $A \subseteq S$ and $i \in A$. For every step
sequence $\omega$ whose first [holding
time](../finite-continuous-time-markov-chains-as-path-pro/ctmc-holding-time.md) from $i$ is positive,
$S_0(i, \omega) > 0$, the [hitting time](ctmc-hitting-time.md) $H_A(i, \omega)$ is $0$. For a rate
matrix and its step law the holding time vanishes only on a null event: when $q(i) > 0$ and the first
clock is nonpositive. For a general matrix it can vanish otherwise: $Q = (1)$ on one state and the
clock $E_0 = 1$ give $S_0 = 0$.
