# Nadel vanishing theorem

Let $X$ be an integral smooth complex projective variety, $L$ an integral divisor and $D$ an
effective $\mathbb{Q}$-divisor on $X$ such that $L - D$ is
[nef and big](nef-and-big-line-bundles.md). Then

$$H^i\bigl(X, \mathcal{O}_X(K_X + L) \otimes \mathcal{J}(D)\bigr) = 0 \qquad (i > 0),$$

where $\mathcal{J}(D)$ is the [multiplier ideal](multiplier-ideal-of-a-q-divisor.md) of $D$.

No normal crossing hypothesis is made on $D$. The analogues for pairs on normal varieties, and the
construction of isolated non-klt centres by which adjoint linear systems separate points, are the
subject of the node [Nadel vanishing for pairs and separation of points by
sections](nadel-vanishing-for-klt-pairs-and-point-separation.md). When $D$ has snc support,
$\mathcal{J}(D) = \mathcal{O}_X(-\lfloor D \rfloor)$ and the statement is the complex case of the
[Kawamata–Viehweg vanishing theorem](kawamata-viehweg-vanishing-theorem.md).

Lazarsfeld's proof: let $\mu \colon X' \to X$ be a log resolution of $D$, $L' = \mu^* L$ and
$D' = \mu^* D$. Then $L' - D'$ is a nef and big $\mathbb{Q}$-divisor and $D'$ has snc support, so the
Kawamata–Viehweg theorem on $X'$ gives
$H^i(X', \mathcal{O}_{X'}(K_{X'} + L' - \lfloor D' \rfloor)) = 0$ for $i > 0$. Since
$\mathcal{O}_{X'}(K_{X'} + L' - \lfloor D' \rfloor) \cong \mathcal{O}_{X'}(K_{X'/X} - \lfloor \mu^* D \rfloor + \mu^*(K_X + L))$,
the projection formula gives
$\mu_* \mathcal{O}_{X'}(K_{X'} + L' - \lfloor D' \rfloor) \cong \mathcal{O}_X(K_X + L) \otimes \mathcal{J}(D)$,
and by the [local vanishing theorem](local-vanishing-for-multiplier-ideals.md) the higher direct
images of this sheaf vanish, so the two cohomology groups agree.

## Depends on

- [Multiplier ideal of an effective Q-divisor](multiplier-ideal-of-a-q-divisor.md)
- [Nef and big line bundles](nef-and-big-line-bundles.md), for nef and big $\mathbb{Q}$-divisors
- [Geometrically reduced variety over a field](../schemes-and-morphisms/varieties-over-a-field/is-variety.md),
  for the underlying complex variety, which the statement takes smooth, projective and integral

## Proof depends on

- [Kawamata–Viehweg vanishing theorem](kawamata-viehweg-vanishing-theorem.md), on a log resolution
- [Local vanishing theorem for multiplier ideals](local-vanishing-for-multiplier-ideals.md)
- [Standard results of coherent cohomology on projective varieties](standard-results-of-coherent-cohomology.md),
  for the projection formula and the Leray spectral sequence

## Sources

- R. Lazarsfeld, "A short course on multiplier ideals", arXiv:0901.0651 (version 1),
  <https://arxiv.org/abs/0901.0651v1>: Theorem 2.4 and its proof, pp. 11–12. See also
  R. Lazarsfeld, *Positivity in Algebraic Geometry I, II*, Ergebnisse der Mathematik und ihrer
  Grenzgebiete 48, 49, Springer, 2004: the chapter "Multiplier Ideal Sheaves" (volume II,
  pp. 139–231).
