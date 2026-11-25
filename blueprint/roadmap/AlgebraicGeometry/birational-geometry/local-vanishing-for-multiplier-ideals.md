# Local vanishing theorem for multiplier ideals

Let $X$ be a smooth complex variety, $D$ an effective $\mathbb{Q}$-divisor on $X$ and
$\mu \colon X' \to X$ a [log resolution](multiplier-ideal-of-a-q-divisor.md) of $D$. Then

$$R^j \mu_* \mathcal{O}_{X'}\bigl(K_{X'/X} - \lfloor \mu^* D \rfloor\bigr) = 0 \qquad (j > 0).$$

For $j = 0$ the direct image is the [multiplier ideal](multiplier-ideal-of-a-q-divisor.md)
$\mathcal{J}(D)$, so that $\mathcal{O}_{X'}(K_{X'/X} - \lfloor \mu^* D \rfloor)$ computes
$\mathcal{J}(D)$ without higher direct images.

Lazarsfeld sketches the proof: one reduces to the case where $X$ is projective and applies the
Kawamata–Viehweg vanishing theorem in that global setting (Positivity II, §9.4.A). Esnault and
Viehweg carry out this argument for the
[relative vanishing theorem for birational morphisms](relative-vanishing-for-birational-morphisms.md),
which gives the statement. On each connected component of $X$, write $D = \Delta / N$ with $\Delta$
an effective integral divisor, Cartier as $X$ is smooth; $\mu^* \Delta$ has snc support, $\mu$ being
a log resolution, and $\lfloor \mu^* \Delta / N \rfloor = \lfloor \mu^* D \rfloor$, so $R^j
\mu_*(\omega_{X'} \otimes \mathcal{O}_{X'}(-\lfloor \mu^* D \rfloor)) = 0$ for $j > 0$. As
$\mathcal{O}_{X'}(K_{X'/X}) = \omega_{X'} \otimes \mu^* \omega_X^{-1}$, the projection formula gives
the vanishing above.

## Depends on

- [Multiplier ideal of an effective Q-divisor](multiplier-ideal-of-a-q-divisor.md), for log
  resolutions, the relative canonical divisor and $\mathcal{J}(D)$
- [Geometrically reduced variety over a field](../schemes-and-morphisms/varieties-over-a-field/is-variety.md),
  for the underlying smooth complex variety; the statement is local on $X$

## Proof depends on

- [Relative vanishing theorem for birational morphisms](relative-vanishing-for-birational-morphisms.md),
  applied on each connected component of $X$ to $\mu$ and an effective Cartier $\Delta$ with $D =
  \Delta / N$ (Esnault–Viehweg, Corollary 6.11 b)); its proof contains the reduction to a projective
  $X$ and the global Kawamata–Viehweg vanishing
- [Standard results of coherent cohomology on projective varieties](standard-results-of-coherent-cohomology.md),
  for the projection formula (item 1)

## Sources

- R. Lazarsfeld, "A short course on multiplier ideals", arXiv:0901.0651 (version 1),
  <https://arxiv.org/abs/0901.0651v1>: Theorem 2.3 and the remark on its proof after the proof of
  Theorem 2.4, pp. 11–12. See also R. Lazarsfeld, *Positivity in Algebraic Geometry I, II*, Ergebnisse
  der Mathematik und ihrer Grenzgebiete 48, 49, Springer, 2004: the chapter "Multiplier Ideal Sheaves"
  (volume II, pp. 139–231), whose §9.4.A the short course cites for the proof.
- H. Esnault and E. Viehweg, *Lectures on Vanishing Theorems*, DMV Seminar 20, Birkhäuser, 1992;
  electronic version on H. Esnault's page, <https://page.mi.fu-berlin.de/esnault/books/esvibuch.pdf>
  (page numbers of the electronic version): Corollary 6.11 b), p. 59.
