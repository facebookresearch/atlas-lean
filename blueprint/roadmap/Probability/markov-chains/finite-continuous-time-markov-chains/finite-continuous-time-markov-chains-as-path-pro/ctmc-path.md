# Path of a continuous-time Markov chain

Let $Q$ be a real square matrix indexed by a set $S$, $i \in S$ and $\omega$ a step sequence, with
[jump chain](ctmc-jump-chain.md) $Y_n$ and [jump times](ctmc-jump-time.md) $T_n$. For $t \ge 0$,
the path is

$$X_t(i, \omega) = Y_n \qquad \text{for the least } n \text{ with } t < T_{n+1},$$

that is, $X_t = Y_n$ when $T_n \le t < T_{n+1}$. If there is no such $n$ ($t$ is at or after the
explosion time $\sup_n T_n$, a null event for a rate matrix on a finite set by
[non-explosion](ae-tendsto-ctmc-jump-time.md)), $X_t$ is a fixed state of $S$ that does not depend on
$i$, $Q$ or $\omega$.
