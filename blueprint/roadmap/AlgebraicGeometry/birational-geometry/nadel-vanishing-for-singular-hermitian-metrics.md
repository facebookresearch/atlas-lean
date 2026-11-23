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
by Hörmander's $L^2$ estimate for singular metrics (Corollary 5.3) on small balls; the same estimate on
$X$, with the metric of $F$ multiplied by $e^{-\chi \circ \psi}$ for a plurisubharmonic exhaustion
function $\psi$ and a convex increasing function $\chi$ growing fast enough, shows that the complex of
global sections is exact in degrees $q \ge 1$. The coherence of $\mathcal{I}(\varphi)$ is also proved
with Corollary 5.3.

For an effective $\mathbb{Q}$-divisor $D = \sum_j a_j D_j$ on a smooth complex algebraic variety, with
local equations $g_j$ of the $D_j$, $\mathcal{I}(\sum_j a_j \log|g_j|)$ is the analytic sheaf
associated with the [multiplier ideal](multiplier-ideal-of-a-q-divisor.md) $\mathcal{J}(D)$
(Lazarsfeld, Proposition 1.8; Demailly (6.23)). Demailly derives from the theorem a vanishing
theorem for these ideals (Theorem 6.25): if $X$ is a projective manifold and $F$ a line bundle such
that $mF = L + D$ for some $m \ge 1$, a nef line bundle $L$ and an effective divisor $D$, then
$H^q(X, \mathcal{O}(K_X + F) \otimes \mathcal{I}(m^{-1} D)) = 0$ for $q > n - \operatorname{nd}(L)$, where
$\operatorname{nd}(L)$ is the largest $k$ with $c_1(L)^k \ne 0$ (6.20).

## Proof depends on

- [L² estimates for the ∂̄ operator](l2-estimates-for-the-dbar-operator.md), for Hörmander's $L^2$
  estimates for singular metrics (Demailly, Corollary 5.3)

## Sources

- J.-P. Demailly, *Analytic Methods in Algebraic Geometry*, Surveys of Modern Mathematics 1, Higher
  Education Press and International Press, 2012; author's version of July 2011,
  <https://www-fourier.univ-grenoble-alpes.fr/~demailly/manuscripts/analmeth_book.pdf>: Definition
  (5.4), p. 35; Proposition (5.7), p. 37; the definition of $\mathcal{I}(h)$ before Theorem (5.11) and
  Theorem (5.11) (Nadel vanishing theorem) with its proof, p. 39; weakly pseudoconvex manifolds,
  §5.A, p. 34; singular metrics and their weights, (3.10)–(3.12), pp. 25–26; (6.20), p. 49;
  (6.23)–(6.25), p. 50.
- R. Lazarsfeld, "A short course on multiplier ideals", arXiv:0901.0651 (version 1),
  <https://arxiv.org/abs/0901.0651v1>: Definition 1.1 and Proposition 1.8, pp. 2 and 5.
