# Basic reproductive ratio with gamma-distributed maturation

Consider a within-host model with healthy target cells $x$, produced at rate $\lambda$ and dying at
per capita rate $d_x$; immature infected cells $w_1, \dots, w_n$, each stage progressing to the
next at per capita rate $m_n$ and dying at per capita rate $d_w$; and mature infected cells $y$,
which infect target cells at rate $\beta x y$ and die at per capita rate $d_y$. With equal stage
rates the maturation time has the Erlang density

$$p(\tau) = \frac{m_n^{\,n}\, \tau^{\,n-1} e^{-m_n \tau}}{(n-1)!},$$

and setting $m_n = n m$ fixes the mean maturation time at $\langle \tau \rangle = 1/m$ independently
of $n$, with standard deviation $1/(m\sqrt{n})$. For constant infectivity $\beta$, the basic
reproductive ratio, the expected number of new infections caused by one infected cell, is

$$R_0 = \frac{\lambda \beta}{d_x d_y} \Bigl(\frac{n m}{n m + d_w}\Bigr)^{\! n},$$

and in the fixed-delay limit $n \to \infty$, where the maturation time is the constant
$\tau = 1/m$,

$$R_0 = \frac{\lambda \beta}{d_x d_y}\, e^{-d_w / m}.$$

For constant drug levels, $R_0 > 1$ implies the infection persists and reaches an equilibrium and
$R_0 < 1$ implies it dies out.

## Proof depends on

- [Arrival times of exponential interarrivals are Erlang](../../../../../Probability/point-processes/poisson-processes/has-law-arrival-time.md)
- [Compound-interest limit in a Banach algebra](../../../../../Analysis/operator-algebras/exponential-limits-and-the-lie-trotter-formula/tendsto-one-add-inv-smul-pow.md)

## Proof sketch

The factor $\bigl(nm/(nm + d_w)\bigr)^n$ is the probability of surviving all $n$ maturation
stages, each a race between progression at rate $nm$ and death at rate $d_w$; it converges to
$e^{-d_w/m}$ as $n \to \infty$, the survival probability over a deterministic waiting time $1/m$.
If immature cells cannot die ($d_w = 0$), $R_0$ does not depend on the maturation rate at all;
otherwise $R_0$ increases with $m$, so slow maturation is costly.

## Sources

- I. A. Neagu, J. Olejarz, M. Freeman, D. I. S. Rosenbloom, M. A. Nowak, A. L. Hill,
  "Life cycle synchronization is a viral drug resistance mechanism",
  PLoS Computational Biology 14 (2018) e1005947, Eqs. (2), (4) and (5),
  <https://doi.org/10.1371/journal.pcbi.1005947> (PMC5813899).
