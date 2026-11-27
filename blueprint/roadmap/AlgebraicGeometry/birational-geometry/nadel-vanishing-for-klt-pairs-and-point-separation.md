# Nadel vanishing for pairs and separation of points by sections

This node is still to be broken down. It covers the forms of Nadel vanishing for pairs on normal
projective varieties and the construction of isolated non-klt centres by which adjoint linear
systems separate points (Angehrn–Siu, in the algebraic form of Kollár). Let $X$ be a normal complex
projective variety of dimension $n$ and $\Delta$ an effective $\mathbb{Q}$-divisor on $X$ such that
$m(K_X + \Delta)$ is Cartier for some $m \ge 1$. A *log resolution of the pair* is a proper
birational $f \colon Y \to X$ from a smooth $Y$ whose exceptional locus is a divisor and for which
$f^{-1}(\operatorname{Supp} \Delta) \cup \operatorname{Ex}(f)$ is a divisor with simple normal
crossings (Kollár, 1.1.3); resolving $X$ alone is not enough (for $X$ smooth and $\Delta$ a cuspidal
curve it does nothing). Write $K_Y = f^*(K_X + \Delta) + \sum_i a_i E_i$, an equality of
$\mathbb{Q}$-divisors for a canonical divisor $K_Y$ and $K_X = f_* K_Y$, the sum running over the
exceptional divisors **and** the strict transforms of the components of $\Delta$, so that the strict
transform of a component of $\Delta$ has $a_i$ equal to minus its coefficient in $\Delta$ (Kollár,
3.3 and Convention 3.3.2). Numerical equivalence would not determine the $a_i$: for $X = Y =
\mathbb{P}^1$ and $\Delta = p + q$ it allows $a_p = -1/2$ and $a_q = -3/2$ instead of $-1$ and $-1$.
$(X, \Delta)$ is klt, or lc, at a point if all $a_i > -1$, or $\ge -1$, for the $E_i$ meeting the
inverse image of a neighbourhood of the point, and the non-klt locus is the set of points where it
is not klt. The targets are:

1. (Nadel vanishing for pairs, Kollár's Theorem 2.16.) If $N$ is a line bundle with $N \equiv K_X +
   \Delta + M$ numerically for a nef and big $\mathbb{Q}$-Cartier $\mathbb{Q}$-divisor $M$, there is
   an ideal sheaf $\mathcal{J} \subset \mathcal{O}_X$, namely $f_* \mathcal{O}_Y(\sum_{a_i \le -1}
   \lceil a_i \rceil E_i)$, whose cosupport is the non-klt locus of $(X, \Delta)$, with $H^i(X,
   \mathcal{J} \otimes N) = 0$ for $i > 0$. The pair is not assumed to be klt: for a klt pair
   $\mathcal{J} = \mathcal{O}_X$.
2. (Isolated non-klt centres, Kollár's Theorem 6.4.) Let $n \ge 1$, $(X, \Delta)$ klt, $N_0$ a nef
   and big $\mathbb{Q}$-Cartier $\mathbb{Q}$-divisor, $x$ a closed point, and $c_1, \dots, c_n > 0$
   with $c_e^e < (N_0^e \cdot Z)$ for every irreducible subvariety $Z \ni x$ of dimension $e \ge 1$
   and $\sum_e e / c_e \le 1$. Then there is an effective $\mathbb{Q}$-Cartier $\mathbb{Q}$-divisor
   $D \equiv N_0$ such that on a neighbourhood of $x$ the pair $(X, \Delta + D)$ is lc, klt outside
   $x$, and not klt at $x$. The bound $n \ge 1$ is needed: for $X = \operatorname{Spec} \mathbb{C}$,
   $\Delta = 0$ and $N_0 = \mathcal{O}$ the numerical hypotheses hold vacuously, but there is no
   prime divisor at all.
3. (Point separation, Kollár's Theorem 5.9.) Under the hypotheses of 1 with $(X, \Delta)$ klt and $M
   = N_0$ nef and big, for $n \ge 1$, two distinct closed points $x_1, x_2$ and constants $c_1,
   \dots, c_n > 0$ with $c_e^e < (N_0^e \cdot Z)$ for every irreducible $Z$ of dimension $e \ge 1$
   through $x_1$ or $x_2$ and $\sum_{e=1}^n 2^{1/e} e / c_e \le 1$, some section of $N$ vanishes at
   exactly one of $x_1, x_2$. The constants must be positive: on $\mathbb{P}^1$, with $\Delta = 0$,
   $N_0 = \mathcal{O}(1)$ and $c_1 = -1$, both inequalities hold, but $N = K_{\mathbb{P}^1} + N_0 =
   \mathcal{O}(-1)$ has no nonzero section.

Item 3 does not follow from 1 and 2 alone: the divisor of 2 controls the pair near one point only,
and is numerically equivalent to all of $N_0$, leaving no positive part for the vanishing. Kollár's
proof first shows that the strict inequalities still hold for $(1 - \varepsilon) N_0$ with $0 <
\varepsilon \ll 1$ (6.6.2); then a **two-point** divisor (Theorem 6.5): after possibly exchanging
$x_1$ and $x_2$, there is an effective $D \equiv (1 - \varepsilon) N_0$ with $x_1$ an isolated point
of the non-klt locus of $(X, \Delta + D)$ and $x_2$ in it (indeed not lc there); finally 1 applied
to $N \equiv K_X + \Delta + D + \varepsilon N_0$ makes $H^0(X, N) \to H^0(X, N \otimes \mathcal{O}_X
/ \mathcal{J})$ surjective. As $x_1$ is isolated in the cosupport, $\mathcal{O}_X / \mathcal{J}$ is
the product of its Artinian component at $x_1$ and its restriction to the rest of the cosupport,
which contains $x_2$; a section of $N \otimes \mathcal{O}_X / \mathcal{J}$ that generates it on the
component at $x_1$ and is zero on the rest lifts to a section of $N$ that is nonzero at $x_1$ and
vanishes at $x_2$. A good expansion has pages for: multiplier ideals of pairs on normal varieties
and the vanishing theorem 1, deduced from the
[Kawamata–Viehweg vanishing theorem](kawamata-viehweg-vanishing-theorem.md) on a log resolution of
the pair; the construction of singular divisors of Kollár's §6, with the reduction to an ample $N_0$
(6.6, Lemma 6.6.1), the cutting down of minimal non-klt centres and the two-point version 6.5; and
the deduction of 3 as above. Angehrn and Siu prove the corresponding results for an ample line
bundle on a compact complex manifold, with other constants (Theorems 0.1 and 0.3).

## Depends on

- [Multiplier ideal of an effective Q-divisor](multiplier-ideal-of-a-q-divisor.md)
- [Nef and big line bundles](nef-and-big-line-bundles.md)

## Proof depends on

- [Kawamata–Viehweg vanishing theorem](kawamata-viehweg-vanishing-theorem.md)
- [Functorial resolution of schemes of finite type in characteristic zero](resolution-of-singularities/functorial-resolution-of-schemes-of-finite-type.md),
  for log resolutions of pairs, after resolving $X$
- [Principalization of ideal sheaves in characteristic zero](resolution-of-singularities/principalization-of-ideal-sheaves.md), for
  making the inverse image of the boundary and the exceptional locus a divisor with simple normal
  crossings

## Sources

- R. Lazarsfeld, "A short course on multiplier ideals", arXiv:0901.0651 (version 1),
  <https://arxiv.org/abs/0901.0651v1>: the remark on multiplier ideals on singular, normal ambient
  varieties, pp. 5–6; Definition 1.25 (klt pairs); §2.
- J.-P. Demailly, *Analytic Methods in Algebraic Geometry*, Surveys of Modern Mathematics 1, Higher
  Education Press and International Press, 2012; author's version of July 2011,
  <https://www-fourier.univ-grenoble-alpes.fr/~demailly/manuscripts/analmeth_book.pdf>: Corollaries
  (5.12) and (5.13), p. 40 (sections of adjoint bundles from weights with isolated poles).
- J. Kollár, "Singularities of pairs", arXiv:alg-geom/9601026 (version 2), in *Algebraic Geometry —
  Santa Cruz 1995*, Proc. Sympos. Pure Math. 62, Part 1, Amer. Math. Soc., 1997: 1.1.3 (log
  resolutions), p. 4; Theorem 2.16, p. 13; 3.3 with Convention 3.3.2 (discrepancies), pp. 15–16;
  Theorems 5.8–5.9 and their proofs, pp. 30–31; Theorems 6.4–6.5, p. 35; 6.6 (Step 0, with Lemma
  6.6.1 and 6.6.2), pp. 35–36.
- U. Angehrn and Y.-T. Siu, "Effective freeness and point separation for adjoint bundles", Invent.
  Math. 122 (1995), 291–308: Theorems 0.1 and 0.3, p. 291 (ample line bundles on compact complex
  manifolds).
- Provenance: Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>)
  states 1 and 2 in this form, with an ideal sheaf whose cosupport is the non-klt locus in place of
  the multiplier ideal, as `GlobalTheory.Published.NadelVanishingAndNonKltDivisor` (the conjunction
  of `NadelVanishingPair` and `IsolatedNonKltDivisor`), and 3 as
  `GlobalTheory.Published.PointSeparationPair`.
