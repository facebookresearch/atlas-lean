# Multiplier ideal of an effective Q-divisor

Let $X$ be a smooth complex algebraic variety and $D = \sum_i a_i D_i$ an effective
[$\mathbb{Q}$-divisor](simple-normal-crossing-divisor.md) on $X$. A *log resolution* of $D$ is a
proper birational morphism $\mu \colon X' \to X$ with $X'$ smooth such that $\mu^* D +
\operatorname{Exc}(\mu)$ has [simple normal crossing support](simple-normal-crossing-divisor.md),
where $\operatorname{Exc}(\mu)$ is the exceptional locus of $\mu$. Its relative canonical divisor
$K_{X'/X} = \det(d\mu)$, the divisor of the Jacobian determinant of $\mu$, is effective, supported
on $\operatorname{Exc}(\mu)$, and linearly equivalent to $K_{X'} - \mu^* K_X$. The *multiplier
ideal* of $D$ is

$$\mathcal{J}(D) = \mu_* \mathcal{O}_{X'}\bigl(K_{X'/X} - \lfloor \mu^* D \rfloor\bigr) \subseteq \mu_* \mathcal{O}_{X'}(K_{X'/X}) = \mathcal{O}_X,$$

an ideal sheaf on $X$ that does not depend on the choice of the log resolution (Lazarsfeld,
Proposition 1.6).

Log resolutions exist: the blow-up sequence $\Pi$ given by
[principalization](resolution-of-singularities/principalization-of-ideal-sheaves.md) of the ideal sheaf of the support of $D$,
with $E = \emptyset$, is one. Indeed, the pull-back of this ideal sheaf is the ideal sheaf of an
effective divisor with snc support whose support is that of $\Pi^* D$; in Kollár's construction this
support is the total exceptional set $\mathrm{Ex}_{\mathrm{tot}}(\Pi)$, which contains
$\operatorname{Exc}(\Pi)$ (Kollár, Theorem 35 and its proof in 72). Demailly appeals to Hironaka's
theorem for the same purpose (Analytic methods, (6.23)).

Lazarsfeld reduces Proposition 1.6, using that any two log resolutions are dominated by a third, to
the case of a divisor $D$ that already has snc support, where for every further log resolution $\mu$
one has $\mu_* \mathcal{O}_{X'}(K_{X'/X} - \lfloor \mu^* D \rfloor) = \mathcal{O}_X(-\lfloor D
\rfloor)$ (Lemma 1.7; he refers to Positivity II, 9.2.19, for the computation).

Lemma 1.7 is a computation of orders along the prime divisors of $X'$. Write $D = \sum_i a_i D_i$,
let $E$ be a prime divisor on $X'$ and $m_i = \operatorname{ord}_E(\mu^* D_i)$. Near a closed point
of $\mu(E)$ choose coordinates $z_1, \dots, z_n$ in which every $D_i$ through that point is
$(z_{c(i)} = 0)$, and write $\mu^* z_k = u^{e_k} v_k$ at the generic point of $E$, with $u$ a
uniformizer and $v_k$ units, so that $m_i = e_{c(i)}$ if $D_i$ contains $\mu(E)$ and $m_i = 0$
otherwise. In $\mu^*(dz_1 \wedge \dots \wedge dz_n) = \mu^*(z_1 \cdots z_n) \bigwedge_k \bigl(e_k
\frac{du}{u} + \frac{dv_k}{v_k}\bigr)$ the factor $\frac{du}{u}$ occurs at most once, so the wedge
product has at most a simple pole along $E$, and $\operatorname{ord}_E(K_{X'/X}) \ge \sum_k e_k - 1
\ge \sum_i m_i - 1$. As $0 \le a_i - \lfloor a_i \rfloor < 1$, it follows that
$\operatorname{ord}_E(K_{X'/X}) \ge \lfloor \sum_i (a_i - \lfloor a_i \rfloor) m_i \rfloor =
\operatorname{ord}_E(\lfloor \mu^* D \rfloor - \mu^* \lfloor D \rfloor)$ when some $m_i > 0$, and
also when all $m_i$ vanish, $K_{X'/X}$ being effective. Hence $\mu^* \lfloor D \rfloor \ge \lfloor
\mu^* D \rfloor - K_{X'/X}$, and, as $\lfloor \mu^* D \rfloor \ge \mu^* \lfloor D \rfloor$,
$\mathcal{O}_{X'}(-\mu^* \lfloor D \rfloor) \subseteq \mathcal{O}_{X'}(K_{X'/X} - \lfloor \mu^* D
\rfloor) \subseteq \mathcal{O}_{X'}(K_{X'/X} - \mu^* \lfloor D \rfloor)$. By the projection formula
and $\mu_* \mathcal{O}_{X'} = \mu_* \mathcal{O}_{X'}(K_{X'/X}) = \mathcal{O}_X$, the outer terms
push forward to $\mathcal{O}_X(-\lfloor D \rfloor)$, and Lemma 1.7 follows.

A common refinement of two log resolutions $\mu_1, \mu_2$ is obtained by resolving the closure of
the graph of the birational map between them and then applying principalization once more to the
ideal of the **reduced union** of the pull-backs of $\operatorname{Supp} D$, of the exceptional loci
of the maps to $X_1$ and $X_2$ and of the exceptional divisors over $X$, so that the result is again
a log resolution, which factors through both. Principalizing only the support of the pull-back of
$D$ would not do: the exceptional divisors need not lie in it, and composing smooth blow-ups need
not keep an old boundary snc (with old boundary $x = 0$ in a threefold, blowing up the smooth curve
$(y, x - z^2)$ gives, in the chart $x - z^2 = uy$, the singular strict transform $uy + z^2 = 0$). On
it the two constructions agree by Lemma 1.7 applied on $X_1$ and on $X_2$, together with the
composition rule $\mu_* (\mathcal{O}_{X'}(K_{X'/X}) \otimes \mathcal{J}(X', \mu^* D)) =
\mathcal{J}(X, D)$ for proper birational $\mu$ (Lemma 1.9). In particular $\mathcal{J}(D) =
\mathcal{O}_X(-\lfloor D \rfloor)$ when $D$ has snc support. Writing $\mu^* D = \sum_i r_i E_i$ and
$K_{X'/X} = \sum_i b_i E_i$ with distinct prime divisors $E_i$ on $X'$, $\mathcal{J}(D)$ is, on each
connected component of $X$, the sheaf of rational functions $f$ with $\operatorname{ord}_{E_i}(f)
\ge \lfloor r_i \rfloor - b_i$ for all $i$ and $f$ otherwise regular; as $b_i > 0$ only for
exceptional $E_i$, such $f$ have no poles on $X$ (Lazarsfeld (1.1) and the discussion after it).
Rounding does not commute with pull-back: for three distinct lines $A_1, A_2, A_3$ through the
origin of $\mathbb{C}^2$ and $D = \frac{2}{3}(A_1 + A_2 + A_3)$, $\mathcal{J}(D)$ is the maximal
ideal of the origin (Example 1.5).

Analytically, if $f_i$ are local equations of the $D_i$, $\mathcal{J}(D)$ is locally the ideal of
holomorphic functions $h$ such that $|h|^2 / \prod_i |f_i|^{2a_i}$ is locally integrable
(Lazarsfeld, Definition 1.1 and Proposition 1.8, the analytic sheaf being the one associated with
$\mathcal{J}(D)$); in the notation of the
[Nadel vanishing theorem for singular hermitian metrics](nadel-vanishing-for-singular-hermitian-metrics.md),
$\mathcal{J}(D) = \mathcal{I}(\varphi)$ for $\varphi = \sum_i a_i \log|f_i|$, which is how Demailly
defines it ((6.23)–(6.24′)).

## Depends on

- [Simple normal crossing divisor](simple-normal-crossing-divisor.md), for $\mathbb{Q}$-divisors, their
  round-down and snc support
- [Principalization of ideal sheaves in characteristic zero](resolution-of-singularities/principalization-of-ideal-sheaves.md), for
  the existence of log resolutions
- [Geometrically reduced variety over a field](../schemes-and-morphisms/varieties-over-a-field/is-variety.md),
  for the underlying smooth complex variety, whose connected components are treated separately

## Proof depends on

- [Functorial resolution of schemes of finite type in characteristic zero](resolution-of-singularities/functorial-resolution-of-schemes-of-finite-type.md),
  to resolve the closure of the graph in the common refinement of two log resolutions
- [Principalization of ideal sheaves in characteristic zero](resolution-of-singularities/principalization-of-ideal-sheaves.md), to
  make the common refinement a log resolution
- [Standard results of coherent cohomology on projective varieties](standard-results-of-coherent-cohomology.md),
  for the projection formula in Lemmas 1.7 and 1.9

## Sources

- R. Lazarsfeld, "A short course on multiplier ideals", arXiv:0901.0651 (version 1),
  <https://arxiv.org/abs/0901.0651v1>: Definition 1.1, Exercise 1.2, log resolutions and Definition
  1.3, pp. 2–3; (1.1) and Example 1.5, p. 4; Proposition 1.6, Lemma 1.7, Proposition 1.8 and Lemma
  1.9, p. 5. See also R. Lazarsfeld, *Positivity in Algebraic Geometry I, II*, Ergebnisse der
  Mathematik und ihrer Grenzgebiete 48, 49, Springer, 2004: the chapter "Multiplier Ideal Sheaves"
  (volume II, pp. 139–231), whose 9.2.19 the short course cites for Lemma 1.7.
- J. Kollár, "Resolution of singularities – Seattle lecture", arXiv:math/0508332 (version 3),
  <https://arxiv.org/abs/math/0508332v3>: Theorem 35, pp. 24–25, and its proof in 72, pp. 42–43;
  Definition 25, pp. 18–19.
- J.-P. Demailly, *Analytic Methods in Algebraic Geometry*, Surveys of Modern Mathematics 1, Higher
  Education Press and International Press, 2012; author's version of July 2011,
  <https://www-fourier.univ-grenoble-alpes.fr/~demailly/manuscripts/analmeth_book.pdf>:
  (6.23)–(6.24′), p. 50; Remark (5.9), pp. 38–39.
