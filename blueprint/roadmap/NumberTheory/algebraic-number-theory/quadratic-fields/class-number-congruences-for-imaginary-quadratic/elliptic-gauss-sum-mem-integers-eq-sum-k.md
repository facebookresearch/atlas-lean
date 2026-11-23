# Integrality of the elliptic Gauss sum

Let $\rho = e^{2\pi i/3}$, let
$\varpi_1 = \int_0^1 (1 - t^3)^{-2/3}\,dt$, let $\wp$ be the Weierstrass function of the lattice
$\varpi_1 \mathbb{Z} + \varpi_1 \rho \mathbb{Z}$, and let
$\varphi(u) = 6\wp(\varpi_1 u)/(9 + \wp'(\varpi_1 u))$. Let $a, b$ be integers with
$a \equiv 1 \pmod 3$ and $b \equiv 0 \pmod 3$ such that $\ell = a^2 - ab + b^2$ is a prime with
$\ell \equiv 7 \pmod 9$ or $\ell \equiv 4 \pmod 9$, and put $\lambda = a + b\rho$. Let
$r_0 \in \mathbb{Z}/\ell\mathbb{Z}$ satisfy $a + b r_0 = 0$, and let
$\chi_\lambda : \mathbb{Z}/\ell\mathbb{Z} \to \mathbb{C}$ be a function such that for every
$t \ne 0$ there is an integer $k \ge 0$ with $\chi_\lambda(t) = \rho^k$ and
$t^{(\ell-1)/3} = r_0^k$. Let $f = \varphi$ if $\ell \equiv 7 \pmod 9$ and $f = 1/\varphi$ if
$\ell \equiv 4 \pmod 9$, and let

$$G = \frac{1}{3} \sum_{r=1}^{\ell-1} \chi_\lambda(r)\,f(r/\lambda).$$

Then $G$ is an algebraic integer lying in the subfield $\mathbb{Q}(\rho, \varphi(1/\lambda))$ of
$\mathbb{C}$, and $G$ equals the sum of $f(r/\lambda)$ over the integers $1 \le r \le \ell - 1$ with
$\chi_\lambda(r) = 1$.

Here $\chi_\lambda$ is the cubic residue character modulo $\lambda$, read through the isomorphism
$\mathbb{Z}[\rho]/(\lambda) \cong \mathbb{Z}/\ell\mathbb{Z}$ that sends $\rho$ to $r_0$; the
integers $1, \dots, \ell - 1$ represent $(\mathbb{Z}[\rho]/(\lambda))^\times$, so $G$ is the
elliptic Gauss sum $G_\lambda(\chi_\lambda, f)$ of the source.

## Sources

- Akihiro Goto, *Congruence Relations Connecting Tate-Shafarevich Groups with Bernoulli-Hurwitz Numbers by Elliptic Gauss Sums in the Eisenstein Integers Case*, INTEGERS 26 (2026), Article A112, Lemma 11.
