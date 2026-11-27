# The $a$-th synthetic order statistic

For $a \in \mathbb{N}$ and a score vector $\omega$ with synthetic scores $\tilde\omega_1, \dots, \tilde\omega_N$,
the $a$-th synthetic order statistic $\tilde S_{(a)}(\omega)$ is the $a$-th smallest synthetic score
counted with multiplicity: the least $\tilde\omega_s$ such that at least $a$ synthetic scores are
$\le \tilde\omega_s$, and $+\infty$ if there is none. For $a = N + 1$ it is $+\infty$, the upper sentinel
([statement](synthetic-order-statistic-succ-eq-top.md)); the lower sentinel $a = 0$ is treated
separately in [the window probability](measure-real-window.md).
