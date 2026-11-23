# Vanishing cutoff factor

For real numbers $a$, $b$, $\delta$ and $x$, the value at $x$
of the vanishing cutoff factor with endpoints $a$, $b$ and width $\delta$ is
$\max\bigl(0, \min\bigl(1, \min((x - a)/\delta, (b - x)/\delta)\bigr)\bigr)$, where division
by $0$ is read as $0$.

It vanishes at $a$ and at $b$. For $\delta > 0$ it equals $1$ on $[a + \delta, b - \delta]$,
an interval that is nonempty when $2\delta \le b - a$. At $\delta = 0$ it is identically
zero.
