# Poincaré–Lelong formula

Let $X$ be a complex manifold of dimension $n$ and $f$ a meromorphic function on $X$ that does not
vanish identically on any connected component of $X$, with divisor
$\operatorname{div}(f) = \sum_j m_j Z_j$: the $Z_j$ are the irreducible components of the zero set and
of the polar set of $f$, and $m_j \in \mathbb{Z}$ is the vanishing order of $f$ along $Z_j$, negative
along the poles. Then $\log|f|$ is locally integrable on $X$ and, as currents of bidegree $(1, 1)$,

$$\frac{i}{\pi}\, \partial\bar\partial \log|f| = \sum_j m_j\, [Z_j],$$

the sum being locally finite. With $d = \partial + \bar\partial$ and
$d^c = \frac{i}{4\pi}(\bar\partial - \partial)$, so that $dd^c = \frac{i}{2\pi}\partial\bar\partial$, this
reads

$$dd^c \log|f|^2 = \sum_j m_j\, [Z_j].$$

Here, for a closed analytic subset $A \subset X$ of pure dimension $p$, the current of integration
$[A]$ acts on smooth compactly supported $(p, p)$-forms $\alpha$ by
$\langle [A], \alpha \rangle = \int_{A_{\mathrm{reg}}} \alpha$. Lelong showed that the regular part
$A_{\mathrm{reg}}$ has locally finite volume near the singular part, so that $[A]$ is well defined, and
that $[A]$ is a closed positive current; its closedness can be deduced from the Skoda–El Mir extension
theorem.

If $f$ is holomorphic, the $m_j$ are positive, $\log|f|$ is plurisubharmonic and the right-hand side
is a positive current (*Complex analytic and differential geometry*, III, after (2.15); *Analytic
methods*, (1.20)). Demailly normalizes $d^c = \frac{1}{2i\pi}(\partial - \bar\partial)$, so that
$dd^c = \frac{i}{\pi}\partial\bar\partial$ and the formula reads $dd^c \log|f| = \sum_j m_j [Z_j]$; the
normalization above is that of Gillet and Soulé. For a meromorphic section $s$ of a holomorphic line
bundle $\mathcal{L}$ with a smooth hermitian metric $\lVert \cdot \rVert$, not vanishing identically on
any component, Gillet and Soulé deduce from the formula that $\log \lVert s \rVert^2$ is locally
integrable and $dd^c [\log \lVert s \rVert^2] = \delta_Y - c_1(\mathcal{L}, \lVert \cdot \rVert)$, where
$Y = \operatorname{div}(s)$, $\delta_Y$ is its current of integration and $c_1$ the first Chern form
(Gillet–Soulé (1.3.1.1); Demailly, *Analytic methods*, (3.11), for holomorphic sections).

Demailly's proof: away from the support of $\operatorname{div}(f)$, $\partial\bar\partial \log|f| = 0$;
near a regular point of $Z_j$ not on the other components, $f = u\, w_1^{m_j}$ in local coordinates
with $u$ invertible, which reduces the formula to the identity
$\frac{i}{\pi}\partial\bar\partial \log|z| = \delta_0$ in $\mathbb{C}$; the difference of the two sides is then
a closed current of order $0$ supported on an analytic set of dimension less than $n - 1$, hence zero
(*Complex analytic and differential geometry*, III (2.10)–(2.11)).

## Depends on

- [Currents of integration and the support theorems](currents-of-integration.md), for currents of
  bidegree $(1, 1)$ and Lelong's currents of integration $[Z_j]$

## Proof depends on

- [Currents of integration and the support theorems](currents-of-integration.md), for Lelong's theorem,
  the fundamental solution of $\partial\bar\partial$ on $\mathbb{C}$ and the support theorem
  (Demailly, Chapter III, Corollary (2.11)) used in the proof

## Sources

- J.-P. Demailly, *Complex Analytic and Differential Geometry*, version of 21 June 2012,
  <https://www-fourier.univ-grenoble-alpes.fr/~demailly/manuscripts/agbook.pdf>: Chapter III, (2.15)
  (Lelong–Poincaré equation, meromorphic case) with its proof, pp. 143–144; (2.5)–(2.7) (currents of
  integration), p. 140; (2.10)–(2.11), p. 141; the normalization of $d^c$ in §3, p. 144; Chapter II,
  (6.12)–(6.14) (divisors of meromorphic functions), pp. 109–110.
- J.-P. Demailly, *Analytic Methods in Algebraic Geometry*, Surveys of Modern Mathematics 1, Higher
  Education Press and International Press, 2012; author's version of July 2011,
  <https://www-fourier.univ-grenoble-alpes.fr/~demailly/manuscripts/analmeth_book.pdf>: (1.17)
  (currents of integration), p. 10; Theorem (1.18) (Skoda–El Mir), p. 11; (1.20) (Lelong–Poincaré
  equation for holomorphic functions), p. 11; (3.10)–(3.11), pp. 25–26.
- H. Gillet and C. Soulé, "Arithmetic intersection theory", Publ. Math. IHÉS 72 (1990), 93–174,
  <http://www.numdam.org/item?id=PMIHES_1990__72__93_0>: 1.1.6 (ii) ($d^c = \frac{i}{4\pi}(\bar\partial -
  \partial)$, $dd^c = \frac{i}{2\pi}\partial\bar\partial$), p. 100; (1.3.1.1), p. 103.
