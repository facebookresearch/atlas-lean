# Negative binomial splitting

For $r_1, r_2 > 0$, $0 < p < 1$ and $k \le n$,

$$\frac{\mathrm{NB}_{r_1, p}(k)\, \mathrm{NB}_{r_2, p}(n - k)}{\mathrm{NB}_{r_1 + r_2, p}(n)} = \mathrm{BB}(n; r_1, r_2)(k),$$

where $\mathrm{NB}_{r, p}$ is the [negative binomial mass function](neg-binomial-pmf.md) and $\mathrm{BB}$
the [beta-binomial mass function](beta-binomial-pmf.md): the conditional law of one component given
the total is beta-binomial and does not depend on $p$.
