# Ohsawa–Takegoshi L² extension theorem

Let $\Omega \subset \mathbb{C}^n$ be a bounded pseudoconvex domain,
$\psi \colon \Omega \to \mathbb{R} \cup \{-\infty\}$ a plurisubharmonic function and
$H \subset \mathbb{C}^n$ a complex hyperplane. There is a constant $C$, depending only on the diameter
of $\Omega$, such that every holomorphic function $f$ on $\Omega \cap H$ with
$\int_{\Omega \cap H} e^{-\psi} |f|^2 \, dV_{n-1} < \infty$ extends to a holomorphic function $F$ on
$\Omega$, $F|_{\Omega \cap H} = f$, satisfying

$$\int_\Omega e^{-\psi} |F|^2 \, dV_n \le C \int_{\Omega \cap H} e^{-\psi} |f|^2 \, dV_{n-1},$$

where $dV_n$ is the Lebesgue measure on $\mathbb{C}^n$ and $dV_{n-1}$ the $(2n-2)$-dimensional Lebesgue
measure on $H$.

Ohsawa and Takegoshi deduce it as an immediate corollary of the extension theorem of their §3, on Stein
manifolds: let $X$ be a Stein manifold of dimension $n$, $\psi$ a plurisubharmonic function on $X$ and
$s$ a holomorphic function on $X$ with $ds \ne 0$ on every branch of $s^{-1}(0)$, and put
$Y_0 = \{x \in X : s(x) = 0,\ ds(x) \ne 0\}$ and $c_k = (-1)^{k(k-1)/2} i^k$. For every holomorphic
$(n-1)$-form $g$ on $Y_0$ with $c_{n-1} \int_{Y_0} e^{-\psi} g \wedge \bar g < \infty$ there is a
holomorphic $n$-form $G$ on $X$ with $G = g \wedge ds$ on $Y_0$ and

$$c_n \int_X e^{-\psi} (1 + |s|^2)^{-2}\, G \wedge \bar G \le 1620\pi\, c_{n-1} \int_{Y_0} e^{-\psi}\, g \wedge \bar g.$$

The proof solves a $\bar\partial$-equation with an $L^2$ estimate for the twisted operator
$\bar\partial \circ \eta$, $\eta$ a positive function (their §2, Proposition 1, a modification of the
Bochner–Kodaira–Nakano technique), through Andreotti and Vesentini's theory of $\bar\partial$ on complete
Kähler manifolds (their §2, Theorem 2).

Demailly gives a general form, following Manivel (Theorem 13.6): let $X$ be a weakly pseudoconvex
complex manifold of dimension $n$ with a Kähler metric $\omega$, $L$ a hermitian line bundle and $E$ a
hermitian vector bundle of rank $r$ on $X$, and $s$ a holomorphic section of $E$, generically transverse
to the zero section, with $Y = \{s = 0,\ \Lambda^r ds \ne 0\}$. Assume that
$i\Theta_L + r\, i\partial\bar\partial \log|s|^2$ is semi-positive and that for some continuous function
$\alpha \ge 1$ one has $i\Theta_L + r\, i\partial\bar\partial \log|s|^2 \ge \alpha^{-1} \{i\Theta_E s, s\} / |s|^2$
and $|s| \le e^{-\alpha}$ on $X$. Then every smooth $\bar\partial$-closed $(0, q)$-form $f$ on $Y$ with
values in $\Lambda^n T^*_X \otimes L$ and $\int_Y |f|^2 |\Lambda^r(ds)|^{-2} dV_\omega < \infty$ is the
restriction of a $\bar\partial$-closed $(0, q)$-form $F$ on $X$ with values in
$\Lambda^n T^*_X \otimes L$, smooth outside $\{s = \Lambda^r ds = 0\}$, such that

$$\int_X \frac{|F|^2}{|s|^{2r} (-\log|s|)^2}\, dV_{X,\omega} \le C_r \int_Y \frac{|f|^2}{|\Lambda^r(ds)|^2}\, dV_{Y,\omega},$$

with a constant $C_r$ depending only on $r$. For a bounded pseudoconvex domain $\Omega \subset \mathbb{C}^n$
and a submanifold $Y$ defined by a section $s$ of a hermitian vector bundle with bounded curvature,
everywhere transverse to the zero section and with $|s| \le e^{-1}$, this gives, for every
plurisubharmonic $\varphi$ on $\Omega$, extensions $F$ of holomorphic functions $f$ on $Y$ with
$\int_\Omega |F|^2 |s|^{-2r} (-\log|s|)^{-2} e^{-\varphi} dV_\Omega \le C \int_Y |f|^2
|\Lambda^r(ds)|^{-2} e^{-\varphi} dV_Y$, where $C$ depends only on the bundle (Corollary 13.9).

## Proof depends on

- [L² estimates for the ∂̄ operator](l2-estimates-for-the-dbar-operator.md), for the twisted a priori
  estimate (Ohsawa–Takegoshi, §2, Proposition 1; Demailly, Lemma 13.1) and the $L^2$ existence theorem
  on complete Kähler manifolds (Ohsawa–Takegoshi, §2, Theorem 2; Demailly, Proposition 13.4)

## Sources

- T. Ohsawa and K. Takegoshi, "On the extension of $L^2$ holomorphic functions", Math. Z. 195 (1987),
  197–204, <https://gdz.sub.uni-goettingen.de/id/PPN266833020_0195>: the Theorem of the introduction,
  p. 197; §2, Proposition 1, p. 199, and Theorem 2, p. 200; the Theorem of §3, p. 200, with its proof
  and the remark deducing the main theorem, pp. 200–203.
- J.-P. Demailly, *Analytic Methods in Algebraic Geometry*, Surveys of Modern Mathematics 1, Higher
  Education Press and International Press, 2012; author's version of July 2011,
  <https://www-fourier.univ-grenoble-alpes.fr/~demailly/manuscripts/analmeth_book.pdf>: §13, Theorem
  (13.6), pp. 125–126, and Corollary (13.9), p. 132.
- Provenance: Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>) uses a related form of
  the extension theorem, for the finite zero set of $n$ sections of a line bundle on a compact
  $n$-dimensional complex manifold carrying a positive line bundle, with an estimate weighted by the
  logarithm of the norm of the sections, as `GlobalTheory.Published.L2ExtensionLogCanonical`.
