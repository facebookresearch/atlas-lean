# Hitting time of a continuous-time Markov chain

Let $Q$ be a real square matrix indexed by a set $S$, $i \in S$, $A \subseteq S$, and $\omega$ a
step sequence, with $X_t = X_t(i, \omega)$ the [path](../finite-continuous-time-markov-chains-as-path-pro/ctmc-path.md)
started at $i$. The hitting time of $A$ is

$$H_A(i, \omega) = \inf\{ t \ge 0 : X_t \in A \} \in [0, \infty],$$

with $\inf \emptyset = \infty$: it is $\infty$ if $A$ is never visited.
