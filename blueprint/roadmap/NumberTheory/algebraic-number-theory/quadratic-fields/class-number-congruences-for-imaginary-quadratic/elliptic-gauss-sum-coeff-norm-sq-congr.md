# Congruences for $|\alpha_\lambda|^2$

Let $\rho = e^{2\pi i/3}$, let
$\varpi_1 = \int_0^1 (1 - t^3)^{-2/3}\,dt$, let $\wp$ be the Weierstrass function of the lattice
spanned by $\varpi_1$ and $\varpi_1\rho$, and put
$\varphi(u) = 6\wp(\varpi_1 u)/(9 + \wp'(\varpi_1 u))$. Put
$\mathrm{Sl}(u) = \varphi(u/(-3\varpi_1))$. Let $a, b$ be integers with $a \equiv 1$ and
$b \equiv 0 \pmod 3$ such that $\ell = a^2 - ab + b^2$ is prime, and put $\lambda = a + b\rho$.
Let $r_0 \in \mathbb{Z}/\ell$ satisfy $a + b r_0 = 0$, and let
$\chi : \mathbb{Z}/\ell \to \mathbb{C}$ be such that for every $t \ne 0$ there is
$j \in \mathbb{N}$ with $\chi(t) = \rho^j$ and $t^{(\ell-1)/3} = r_0^j$. Let $f = \varphi$ if
$\ell \equiv 7 \pmod 9$ and $f = 1/\varphi$ otherwise, and put
$G = \frac13 \sum_{0 < r < \ell} \chi(r) f(r/\lambda)$,
$\tilde\lambda = \prod_{0 < r < \ell,\ \chi(r) = 1} \varphi(r/\lambda)$ and
$\alpha = G/\tilde\lambda^2$. Let $k = 2(\ell-1)/3$, and let $C$ and $D$ be the coefficients of
$u^k$ in the Taylor expansions at $0$ of $\mathrm{Sl}(u)$ and of $\mathrm{Sl}(u)^{-1} - u^{-1}$.
If $\ell \equiv 7 \pmod 9$, there are integers $m, m'$ prime to $\ell$ with
$m(|\alpha|^2 - (\overline{\chi(3)}\,C)^2/9) \in \lambda\mathbb{Z}[\rho]$ and
$m'(|\alpha|^2 - (3^{(\ell-7)/6} C)^2) \in \ell\mathbb{Z}$. If $\ell \equiv 4 \pmod 9$, there are
integers $m, m'$ prime to $\ell$ with $m(|\alpha|^2 - (\chi(3) D)^2/9) \in \lambda\mathbb{Z}[\rho]$
and $m'(|\alpha|^2 - (3^{(\ell-4)/3} D)^2) \in \ell\mathbb{Z}$.

Here $\lambda\bar\lambda = \ell$, $\rho \mapsto r_0$ identifies $\mathbb{Z}[\rho]/(\lambda)$ with
$\mathbb{Z}/\ell$, $\chi$ is the cubic residue character $\chi_\lambda$ modulo $\lambda$, $G$ is
the elliptic Gauss sum $G_\lambda(\chi_\lambda, f)$ and $\alpha = \alpha_\lambda$ its coefficient,
so the statement gives congruences modulo $\lambda$ and modulo $\ell$. At $u = 0$, where $\wp$ has
a pole, both functions take the value $0$, their limit there, and $C$, $D$ are their $k$-th
derivatives at $0$ divided by $k!$.

## Sources

- Akihiro Goto, *Congruence Relations Connecting Tate-Shafarevich Groups with Bernoulli-Hurwitz Numbers by Elliptic Gauss Sums in the Eisenstein Integers Case*, INTEGERS 26 (2026), Article A112, Lemma 12.
