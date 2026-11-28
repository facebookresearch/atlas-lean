# McCann's threshold $m \ge 1 - 1/d$ for porous-medium energies

Let $d \ge 1$ and $0 < m < 1$. Then $A(s) = s^m/(m-1)$ satisfies
[McCann's condition (A1)](mc-cann-condition.md) if and only if

$$m \ge 1 - \frac{1}{d}.$$

The [dilation profile](dilation-profile-porous-medium.md) is $-\lambda^{d(1-m)}/(1-m)$, which is
convex exactly when $\lambda \mapsto \lambda^{d(1-m)}$ is concave, that is when $d(1-m) \le 1$; if
$d(1-m) > 1$ the strict convexity of that power at the midpoint of $1$ and $2$ contradicts
convexity of the profile. At the endpoint $m = 1 - 1/d$, $A$ is a positive multiple of McCann's
Brunn–Minkowski choice $A(s) = -s^{(d-1)/d}$ (his Remark 2.4). The energy $\int \rho^m/(m-1)$
drives the fast diffusion equation $\partial_t \rho = \Delta \rho^m$ for $m < 1$.

Together with [the case $m > 1$](mc-cann-condition-porous-medium-of-one-l.md) and
[the entropy](mc-cann-condition-entropy.md) $s \log s$, the limit as $m \to 1$ of
$(s^m - s)/(m - 1)$ (adding a multiple of $s$ to $A$ adds a constant to its dilation profile, so it
does not change the condition), this gives the full range $m \ge 1 - 1/d$ of displacement-convex
power energies.

## Sources

- R. J. McCann, *A convexity principle for interacting gases*, Adv. Math. 128 (1997), 153–179, condition (A1) and Remark 2.4.
