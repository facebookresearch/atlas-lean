# Growth rate of the fixed-delay infection model

In the delay formulation of the within-host model, where newly infected cells become productive
after a fixed maturation time $\tau$,

$$\begin{aligned}
\dot x(t) &= \lambda - \beta(t)\,x(t)\,y(t) - d_x x(t), \\
\dot y(t) &= \beta(t-\tau)\,x(t-\tau)\,y(t-\tau)\,e^{-d_w \tau} - d_y\, y(t),
\end{aligned}$$

early infection, before target cells are depleted, grows or decays like $e^{r_0 t}$, where the
exponent $r_0$ solves the characteristic equation

$$R_0 = \Bigl(1 + \frac{r_0}{d_y}\Bigr) e^{\,r_0 \tau},$$

with $R_0$ the basic reproductive ratio at the constant infectivity in force. The right-hand side
is increasing in $r_0$ on $r_0 > -d_y$, where it takes every positive value, and is nonpositive for $r_0 \le -d_y$; it equals $1$ at $r_0 = 0$, so the unique real root $r_0$ lies in $(-d_y, \infty)$ and has the sign of $R_0 - 1$.

## Depends on

- [Basic reproductive ratio with gamma-distributed maturation](basic-reproductive-ratio-with-gamma-distributed-maturation.md)

## Remarks

The equation says that an infected cell, which survives for an exponential time of mean $1/d_y$
after maturing, must leave $R_0$ offspring discounted by the delay factor $e^{r_0 \tau}$. The delay
is what makes periodic therapy more than a question of average drug level: if $\beta(t)$ is
periodic with period $T$, a strain whose maturation time is close to an integer multiple of $T$
repeatedly reaches its productive phase in the same part of the dosing cycle, so the time-averaged
reproductive ratio $\bar R_0 = R_0(1-f)$ over a drug that is on for a fraction $f$ of the time is
neither necessary nor sufficient for persistence; the correct threshold comes from the Floquet-type
analogue of the equation above.

## Sources

- I. A. Neagu, J. Olejarz, M. Freeman, D. I. S. Rosenbloom, M. A. Nowak, A. L. Hill,
  "Life cycle synchronization is a viral drug resistance mechanism",
  PLoS Computational Biology 14 (2018) e1005947, Eqs. (3) and (6),
  <https://doi.org/10.1371/journal.pcbi.1005947> (PMC5813899).
