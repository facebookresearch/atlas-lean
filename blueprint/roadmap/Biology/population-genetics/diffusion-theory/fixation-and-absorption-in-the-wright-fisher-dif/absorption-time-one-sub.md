# Reflecting the frequency path leaves the absorption time unchanged

For every real process $(X_t)_{t \ge 0}$ on $\Omega$, with no condition on $X$, the
[absorption time](absorption-time.md) of the reflected process $1 - X$ is that of $X$: for every
outcome $\omega$,

$$\inf\{t \ge 0 : 1 - X_t(\omega) \in \{0, 1\}\} = \inf\{t \ge 0 : X_t(\omega) \in \{0, 1\}\},$$

since $1 - X_t(\omega) \in \{0, 1\}$ exactly when $X_t(\omega) \in \{1, 0\}$: reflection swaps the
two absorbing states. Both infima use the convention $\inf \emptyset = 0$, so the identity also
holds for paths that are never absorbed.
