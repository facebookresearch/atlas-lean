# $\mathrm{Sl}$ and $\mathrm{ArcSl}$ are inverse on the real segment

Let
$\rho = e^{2\pi i/3}$, let $\varpi_1 = \int_0^1 (1 - t^3)^{-2/3}\,dt$, let $\wp$ be the
Weierstrass function of the lattice spanned by $\varpi_1$ and $\varpi_1\rho$, and put
$\varphi(u) = 6\wp(\varpi_1 u)/(9 + \wp'(\varpi_1 u))$. For real $x$ put
$\mathrm{Sl}(x) = \varphi(x/(-3\varpi_1))$, and for real $t$ put
$\mathrm{ArcSl}(t) = \int_0^t (1 - s^3)^{-2/3}\,ds$, so that $\varpi_1 = \mathrm{ArcSl}(1)$. Then:
for every $t \in [0, 1]$ the series $\sum_{n \ge 0} (-1)^n \binom{-2/3}{n} t^{3n+1}/(3n+1)$ has
sum $\mathrm{ArcSl}(t)$, where $\binom{-2/3}{n}$ is the generalized binomial coefficient; for
every $x \in [0, \varpi_1]$, $\mathrm{Sl}(x)$ is a real number $s \in [0, 1]$ with
$\mathrm{ArcSl}(s) = x$; and for every $t \in [0, 1]$, $\mathrm{ArcSl}(t) \in [0, \varpi_1]$ and
$\mathrm{Sl}(\mathrm{ArcSl}(t)) = t$.

At $x = 0$, where $\wp$ has a pole, the values $\wp(0)$ and $\wp'(0)$ are taken to be $0$, so
$\mathrm{Sl}(0) = 0$.

## Sources

- Akihiro Goto, *Congruence Relations Connecting Tate-Shafarevich Groups with Bernoulli-Hurwitz Numbers by Elliptic Gauss Sums in the Eisenstein Integers Case*, INTEGERS 26 (2026), Article A112, Lemma 6 (`integers-2026-A112-lem-6`).
