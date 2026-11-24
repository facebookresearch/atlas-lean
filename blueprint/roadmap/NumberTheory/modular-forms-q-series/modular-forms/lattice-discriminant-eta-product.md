# Jacobi's product formula for the discriminant of a lattice

For $\tau$ in the upper half-plane let

$$g_2(\tau) = 60 \sum_{(m, n) \neq (0, 0)} \frac{1}{(m\tau + n)^4}, \qquad g_3(\tau) = 140 \sum_{(m, n) \neq (0, 0)} \frac{1}{(m\tau + n)^6}$$

be the invariants of the lattice $\mathbb{Z}\tau + \mathbb{Z}$, the sums running over the pairs of integers other than
$(0, 0)$, and let $\eta(\tau) = e^{\pi i \tau / 12} \prod_{n \ge 1} (1 - e^{2\pi i n \tau})$ be the Dedekind eta function.
Then

$$g_2(\tau)^3 - 27 g_3(\tau)^2 = (2\pi)^{12} \eta(\tau)^{24} = (2\pi)^{12} \, q \prod_{n \ge 1} (1 - q^n)^{24}, \qquad q = e^{2\pi i \tau}.$$

Indeed, let $E_k(\tau) = \frac{1}{2} \sum_{\gcd(c, d) = 1} (c\tau + d)^{-k}$ be the normalised Eisenstein series, the sum
running over the coprime pairs of integers. Writing each pair $(m, n) \neq (0, 0)$ as $r (c, d)$, with $r = \gcd(m, n)$ and
$(c, d)$ coprime, gives $\sum_{(m, n) \neq (0, 0)} (m\tau + n)^{-k} = 2 \zeta(k) E_k(\tau)$ for $k = 4, 6$, and the
[even zeta values](../../zeta-l-functions/riemann-zeta/zeta-even-integers-bernoulli.md) $\zeta(4) = \pi^4/90$ and $\zeta(6) = \pi^6/945$ give
$g_2 = \frac{4\pi^4}{3} E_4$ and $g_3 = \frac{8\pi^6}{27} E_6$. Hence
$g_2^3 - 27 g_3^2 = \frac{64 \pi^{12}}{27} (E_4^3 - E_6^2) = (2\pi)^{12} (E_4^3 - E_6^2)/1728$, and the formula is the
[identity $\Delta = (E_4^3 - E_6^2)/1728$](discriminant-eq-eisenstein-cube-sub-sq.md) for the modular discriminant
$\Delta = \eta^{24}$.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Even zeta values and Bernoulli numbers](../../zeta-l-functions/riemann-zeta/zeta-even-integers-bernoulli.md), for $\zeta(4) = \pi^4/90$ and $\zeta(6) = \pi^6/945$
- [The modular discriminant in terms of Eisenstein series](discriminant-eq-eisenstein-cube-sub-sq.md), for $\eta^{24} = (E_4^3 - E_6^2)/1728$

## Sources

- C. L. Siegel, *Lectures on advanced analytic number theory*, notes by S. Raghavan, Tata Institute of
  Fundamental Research Lectures on Mathematics 23, Bombay (1961, reissued 1965),
  <https://www.math.tifr.res.in/~publ/ln/tifr23.pdf> (copy:
  <https://www-users.cse.umn.edu/~garrett/m/mfms/notes_2013-14/Siegel_AdvAnNoTh.pdf>), Chapter 1, §2, p. 14:
  for the period pair $(1, z)$, $(2\pi)^{12} \eta^{24}(z) = g_2^3 - 27 g_3^2$.
- D. Zagier, *Elliptic modular forms and their applications*, in *The 1-2-3 of Modular Forms*,
  Universitext, Springer (2008), 1–103,
  <https://people.mpim-bonn.mpg.de/zagier/files/doi/10.1007/978-3-540-74119-0_1/fulltext.pdf>: §2.1,
  formulas (9)–(11), $E_k(z) = \frac{1}{2} \sum_{(c, d) = 1} (cz + d)^{-k}$ and
  $G_k(z) = \frac{1}{2} \sum_{(m,n) \neq (0,0)} (mz + n)^{-k} = \zeta(k) E_k(z)$; §2.4, the definition (22) of $\Delta$ and
  formula (23), $\Delta = \frac{1}{1728}(E_4^3 - E_6^2)$ (pp. 20–21).
