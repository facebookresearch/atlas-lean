# Stopped discounted process of the jump–hold chain

Let $S$ be a set, $q : S \to \mathbb{R}$, $V : S \to [0, \infty]$, $c \in \mathbb{R}$ and
$A \subseteq S$. For $n \in \mathbb{N}$, a state $x \in S$ and a step sequence
$\omega = ((\xi_k, E_k))_{k \in \mathbb{N}}$, the stopped discounted process
$D_n(x, \omega) \in [0, \infty]$ is defined by recursion on the first step:

$$D_0(x, \omega) = V(x), \qquad
D_{n+1}(x, \omega) = \begin{cases} V(x) & \text{if } x \in A, \\
e^{-c E_0 / q(x)}\, D_n\bigl(\xi_0(x), \theta_1 \omega\bigr) & \text{if } x \notin A, \end{cases}$$

where $\theta_1 \omega = (\omega_1, \omega_2, \dots)$ is the
[shift](../../../Probability/markov-chains/finite-continuous-time-markov-chains/finite-continuous-time-markov-chains-as-path-pro/ctmc-shift.md)
of $\omega$ by one step and the product is taken in $[0, \infty]$. With the convention $a / 0 = 0$,
the factor $e^{-c E_0 / q(x)}$ is $1$ when $q(x) = 0$.

Unfolding the recursion gives, for all such $q$, $V$, $c$ and $A$,

$$D_n(x, \omega) = e^{-c T_{n \wedge \sigma}}\, V(Y_{n \wedge \sigma}),$$

where $Y_k$ is the [jump chain](../../../Probability/markov-chains/finite-continuous-time-markov-chains/finite-continuous-time-markov-chains-as-path-pro/ctmc-jump-chain.md)
and $T_k$ are the [jump times](jump-time.md) started at $x$, and $\sigma = \min\{k : Y_k \in A\}$ is
the first entrance time of the jump chain into $A$, with $\sigma = \infty$ if it never enters $A$:
see the process [before the first entrance](discounted-stop-eq-of-forall-not-mem.md) and
[after it](discounted-stop-eq-of-hit.md).
