# Theta transformation of a Gaussian sum with a linear term

For every complex number $a$ with $\operatorname{Re} a > 0$ and every complex number $b$,

$$\sum_{n \in \mathbb{Z}} e^{-\pi a n^2 + 2\pi b n} = \frac{1}{a^{1/2}} \sum_{n \in \mathbb{Z}} e^{-\pi (n + i b)^2 / a},$$

where $a^{1/2} = \exp\bigl(\tfrac{1}{2} \log a\bigr)$, with the principal branch of the logarithm.

## Sources

- C. L. Siegel, *Lectures on advanced analytic number theory*, notes by S. Raghavan, Tata Institute of
  Fundamental Research Lectures on Mathematics 23, Bombay (1961, reissued 1965),
  <https://www.math.tifr.res.in/~publ/ln/tifr23.pdf> (copy:
  <https://www-users.cse.umn.edu/~garrett/m/mfms/notes_2013-14/Siegel_AdvAnNoTh.pdf>), Chapter 1, §4,
  formulas (50)–(52) (pp. 34–35): the theta transformation formula
  $\sum_{n} e^{-\pi \xi (n + v)^2} = \xi^{-1/2} \sum_{n} e^{-\pi n^2 / \xi + 2\pi i n v}$, valid for complex $v$ and complex
  $\xi$ with $\operatorname{Re} \xi > 0$, $\sqrt{\xi}$ being the branch that is positive for real $\xi > 0$, proved by the
  Poisson summation formula. It is the identity above for $a = \xi$ and $b = -\xi v$, multiplied by
  $e^{-\pi \xi v^2}$.
