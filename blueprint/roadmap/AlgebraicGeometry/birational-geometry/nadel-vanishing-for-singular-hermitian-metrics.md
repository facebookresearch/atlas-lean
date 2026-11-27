# Nadel vanishing theorem for singular hermitian metrics

**Multiplier ideal sheaves.** Let $\varphi$ be a plurisubharmonic function on an open subset $\Omega$ of
a complex manifold $X$ of dimension $n$. Its multiplier ideal sheaf
$\mathcal{I}(\varphi) \subset \mathcal{O}_\Omega$ is the sheaf of germs of holomorphic functions $f$
such that $|f|^2 e^{-2\varphi}$ is integrable with respect to the Lebesgue measure in local
coordinates near the point. It is a coherent ideal sheaf (Nadel; Demailly, Proposition 5.7).

**Singular hermitian metrics.** A singular hermitian metric $h$ on a holomorphic line bundle $F$ over
$X$ is given in every trivialization $\theta \colon F|_\Omega \cong \Omega \times \mathbb{C}$ by
$\lVert \xi \rVert_h = |\theta(\xi)|\, e^{-\varphi(x)}$ for $\xi \in F_x$, with a locally integrable weight
$\varphi$; its curvature current is $\frac{i}{2\pi}\Theta_{F,h} = \frac{i}{\pi}\partial\bar\partial\varphi$.
For plurisubharmonic weights the ideal sheaves $\mathcal{I}(\varphi)$ do not depend on the
trivialization and glue to a coherent ideal sheaf $\mathcal{I}(h)$ on $X$.

**Theorem (Nadel).** Let $(X, \omega)$ be a weakly pseudoconvex Kähler manifold, that is, a complex
manifold with a Kähler metric $\omega$ and a smooth plurisubharmonic exhaustion function. Let $F$ be a
holomorphic line bundle on $X$ with a singular hermitian metric $h$ whose curvature current satisfies
$i\Theta_{F,h} \ge \varepsilon\omega$ for some continuous positive function $\varepsilon$ on $X$, so that
its weights are plurisubharmonic. Then

$$H^q\bigl(X, \mathcal{O}(K_X + F) \otimes \mathcal{I}(h)\bigr) = 0 \qquad (q \ge 1).$$

Every compact complex manifold is weakly pseudoconvex, with the exhaustion function $0$, and so is
every Stein manifold. Demailly's proof: the $(n, q)$-forms $u$ with values in $F$ and measurable
coefficients such that $|u|^2 e^{-2\varphi}$ and $|\bar\partial u|^2 e^{-2\varphi}$ are locally
integrable form a resolution of $\mathcal{O}(K_X + F) \otimes \mathcal{I}(h)$ by fine sheaves, exact
by Hörmander's $L^2$ estimate for singular metrics (Corollary 5.3) on small balls. On $X$ itself the
constant of Corollary 5.3 is not available, as a continuous positive $\varepsilon$ on a noncompact
manifold need not be bounded below by a positive constant; the global step uses instead Theorem 5.2,
whose estimate involves the sum $\gamma_1 + \dots + \gamma_q \ge q\varepsilon(x)$ of the smallest
curvature eigenvalues and which extends to singular metrics by regularization (the remark after it).
Multiplying the metric of $F$ by $e^{-\chi \circ \psi}$, for a plurisubharmonic exhaustion function
$\psi$ and a convex increasing function $\chi$, does not decrease the curvature, and for $\chi$
growing fast enough it makes $\int_X (q\varepsilon)^{-1} |g|^2 e^{-2\varphi - \chi \circ \psi}$
finite for a given global section $g$, $(q\varepsilon)^{-1}$ being bounded on the compact sublevel
sets of $\psi$; so the complex of global sections is exact in degrees $q \ge 1$. The coherence of
$\mathcal{I}(\varphi)$ is also proved with Corollary 5.3 (Demailly, Proposition 5.7): on a small
ball, by the
[strong Noetherian property](../../Analysis/complex-analysis/several-complex-variables/strong-noetherian-property-of-coherent-analytic-sheaves.md)
of coherent analytic sheaves, the holomorphic functions $f$ with $\int |f|^2 e^{-2\varphi} < \infty$
generate a coherent ideal sheaf $\mathcal{J} \subseteq \mathcal{I}(\varphi)$; Corollary 5.3 gives
$\mathcal{I}(\varphi)_x \subseteq \mathcal{J}_x + \mathfrak{m}_x^{s+1}$ for every $s$, and
[Krull's intersection theorem](../../RingTheory/local-rings/krull-intersection-theorem.md) for
$\mathcal{O}_{X,x} / \mathcal{J}_x$ gives $\mathcal{J}_x = \mathcal{I}(\varphi)_x$.

For an effective $\mathbb{Q}$-divisor $D = \sum_j a_j D_j$ on a smooth complex algebraic variety, with
local equations $g_j$ of the $D_j$, $\mathcal{I}(\sum_j a_j \log|g_j|)$ is the analytic sheaf
associated with the [multiplier ideal](multiplier-ideal-of-a-q-divisor.md) $\mathcal{J}(D)$
(Lazarsfeld, Proposition 1.8; Demailly (6.23)).

## Depends on

- [Currents of integration and the support theorems](currents-of-integration.md), for the curvature
  current of a singular metric and the inequality $i\Theta_{F,h} \ge \varepsilon\omega$ in the sense
  of currents
- [Simple normal crossing divisor](simple-normal-crossing-divisor.md), for $\mathbb{Q}$-divisors
- [Multiplier ideal of an effective Q-divisor](multiplier-ideal-of-a-q-divisor.md), for
  $\mathcal{J}(D)$

## Proof depends on

- [L² estimates for the ∂̄ operator](l2-estimates-for-the-dbar-operator.md), for Hörmander's $L^2$
  estimates: Corollary 5.3 on small balls, for the exactness of the resolution and the coherence of
  $\mathcal{I}(\varphi)$, and, on $X$, Theorem 5.2 with a variable lower bound of the curvature,
  extended to singular metrics by regularization (Demailly, §5.A), for the vanishing of the
  cohomology of the global sections
- [Multiplier ideal of an effective Q-divisor](multiplier-ideal-of-a-q-divisor.md), for its analytic
  description (Lazarsfeld, Proposition 1.8), which identifies $\mathcal{I}(\sum_j a_j \log|g_j|)$
  with the analytic sheaf of $\mathcal{J}(D)$
- [Strong Noetherian property of coherent analytic sheaves](../../Analysis/complex-analysis/several-complex-variables/strong-noetherian-property-of-coherent-analytic-sheaves.md),
  for the coherent ideal sheaf generated by the $L^2$ holomorphic functions in the proof of the
  coherence of $\mathcal{I}(\varphi)$ (Demailly, Proposition 5.7)
- [Krull's intersection theorem for finitely generated modules over a Noetherian local ring](../../RingTheory/local-rings/krull-intersection-theorem.md),
  in the stalks $\mathcal{O}_{X,x}$, for the same proof

## Sources

- J.-P. Demailly, *Analytic Methods in Algebraic Geometry*, Surveys of Modern Mathematics 1, Higher
  Education Press and International Press, 2012; author's version of July 2011,
  <https://www-fourier.univ-grenoble-alpes.fr/~demailly/manuscripts/analmeth_book.pdf>: Definition
  (5.4), p. 35; Proposition (5.7), p. 37; the definition of $\mathcal{I}(h)$ before Theorem (5.11) and
  Theorem (5.11) (Nadel vanishing theorem) with its proof, p. 39; weakly pseudoconvex manifolds,
  §5.A, p. 34; singular metrics and their weights, (3.10)–(3.12), pp. 25–26; (6.23), p. 50.
- R. Lazarsfeld, "A short course on multiplier ideals", arXiv:0901.0651 (version 1),
  <https://arxiv.org/abs/0901.0651v1>: Definition 1.1 and Proposition 1.8, pp. 2 and 5.
