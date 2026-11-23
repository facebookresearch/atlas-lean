# Jacobi's product formula for the discriminant of a lattice

For $\tau$ in the upper half-plane let

$$g_2(\tau) = 60 \sum_{(m, n) \neq (0, 0)} \frac{1}{(m\tau + n)^4}, \qquad g_3(\tau) = 140 \sum_{(m, n) \neq (0, 0)} \frac{1}{(m\tau + n)^6}$$

be the invariants of the lattice $\mathbb{Z}\tau + \mathbb{Z}$, the sums running over the pairs of integers other than
$(0, 0)$, and let $\eta(\tau) = e^{\pi i \tau / 12} \prod_{n \ge 1} (1 - e^{2\pi i n \tau})$ be the Dedekind eta function.
Then

$$g_2(\tau)^3 - 27 g_3(\tau)^2 = (2\pi)^{12} \eta(\tau)^{24} = (2\pi)^{12} \, q \prod_{n \ge 1} (1 - q^n)^{24}, \qquad q = e^{2\pi i \tau}.$$

In terms of the Eisenstein series $E_k$ normalised to have constant term $1$, the identities
$\sum_{(m, n) \neq (0, 0)} (m\tau + n)^{-k} = 2 \zeta(k) E_k(\tau)$ for $k = 4, 6$ and the
[even zeta values](../../zeta-l-functions/riemann-zeta/zeta-even-integers-bernoulli.md) $\zeta(4) = \pi^4/90$ and $\zeta(6) = \pi^6/945$ give
$g_2 = \frac{4\pi^4}{3} E_4$ and $g_3 = \frac{8\pi^6}{27} E_6$, so the formula is the identity
$\Delta = (E_4^3 - E_6^2)/1728$ for $\Delta(\tau) = q \prod_{n \ge 1} (1 - q^n)^{24}$. Zagier proves the latter from
the modularity of $\Delta$ in weight $12$ (his Proposition 7), the dimension bound $\dim M_{12}(\mathrm{SL}_2(\mathbb{Z})) \le 2$
for the modular forms of weight $12$ (his Corollary 1 to Proposition 2), by which $M_{12}(\mathrm{SL}_2(\mathbb{Z}))$ is spanned by
$E_4^3$ and $E_6^2$, and the first coefficients of the $q$-expansions $E_4^3 = 1 + 720 q + \cdots$,
$E_6^2 = 1 - 1008 q + \cdots$ and $\Delta = q + \cdots$, the coefficient of $q$ in $\Delta$ being
[$\tau(1) = 1$](ramanujan-tau-function/one.md).

## Depends on

This node has no prerequisites.

## Proof depends on

- [Even zeta values and Bernoulli numbers](../../zeta-l-functions/riemann-zeta/zeta-even-integers-bernoulli.md), for $\zeta(4) = \pi^4/90$ and $\zeta(6) = \pi^6/945$
- [Normalisation of the Ramanujan $\tau$-function](ramanujan-tau-function/one.md), only for the coefficient $1$ of $q$ in $\Delta$

## Sources

- C. L. Siegel, *Lectures on advanced analytic number theory*, notes by S. Raghavan, Tata Institute of
  Fundamental Research Lectures on Mathematics 23, Bombay (1961, reissued 1965),
  <https://www.math.tifr.res.in/~publ/ln/tifr23.pdf> (copy:
  <https://www-users.cse.umn.edu/~garrett/m/mfms/notes_2013-14/Siegel_AdvAnNoTh.pdf>), Chapter 1, §2, p. 14:
  for the period pair $(1, z)$, $(2\pi)^{12} \eta^{24}(z) = g_2^3 - 27 g_3^2$.
- D. Zagier, *Elliptic modular forms and their applications*, in *The 1-2-3 of Modular Forms*,
  Universitext, Springer (2008), 1–103,
  <https://people.mpim-bonn.mpg.de/zagier/files/doi/10.1007/978-3-540-74119-0_1/fulltext.pdf>: §2.1,
  formulas (10) and (11), $G_k(z) = \frac{1}{2} \sum_{(m,n) \neq (0,0)} (mz + n)^{-k} = \zeta(k) E_k(z)$; §2.4, the
  definition (22) of $\Delta$, Proposition 7 ($\Delta$ is a modular form of weight $12$) and formula (23),
  $\Delta = \frac{1}{1728}(E_4^3 - E_6^2)$, with its proof from Corollary 1 to Proposition 2 (§1.3) (pp. 20–21).
