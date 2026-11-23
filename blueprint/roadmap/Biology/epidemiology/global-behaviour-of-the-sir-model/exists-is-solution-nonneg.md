# Forward-global nonnegative SIR solutions

For $\gamma \ge 0$, any real $\beta$ and $N$, and every nonnegative initial state $(S_0, I_0, R_0)$, the
SIR system has a solution with these initial values, with two-sided derivatives at every $t \ge 0$, whose
compartments stay nonnegative and keep the total $S_0 + I_0 + R_0$ for all $t \ge 0$, and along which $S$
(respectively $I$) is positive at a time $t \ge 0$ if and only if $S_0 > 0$ (respectively $I_0 > 0$). The
epidemiological domain $\beta \ge 0$, $\gamma > 0$, $N > 0$, $S_0 + I_0 + R_0 = N$ is a special case.

Proof: take the maximal solution through $(S_0, I_0, R_0)$ at time $0$, defined on an open interval $J$,
which leaves every compact set at each end of $J$. Over $[0, T] \cap J$ it stays in the compact set
$[0, T] \times \Delta$, where $\Delta$ is the simplex of nonnegative states with total
$S_0 + I_0 + R_0$. If some $T \ge 0$ were not in $J$, every forward time of $J$ would be below $T$, and
the solution could not leave $[0, T] \times \Delta$, a contradiction.
