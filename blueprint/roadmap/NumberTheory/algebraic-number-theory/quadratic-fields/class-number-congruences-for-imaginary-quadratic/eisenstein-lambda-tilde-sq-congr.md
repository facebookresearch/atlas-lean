# Congruence for the square of $\tilde\lambda$

Let $\rho = e^{2\pi i/3}$, let
$\varpi_1 = \int_0^1 (1 - t^3)^{-2/3}\,dt$, let $\wp$ be the Weierstrass function of the lattice
spanned by $\varpi_1$ and $\varpi_1\rho$, and put
$\varphi(u) = 6\wp(\varpi_1 u)/(9 + \wp'(\varpi_1 u))$. Let $a, b$ be integers with $a \equiv 1$ and
$b \equiv 0 \pmod 3$ such that $\ell = a^2 - ab + b^2$ is prime, and put $\lambda = a + b\rho$.
Let $r_0 \in \mathbb{Z}/\ell$ satisfy $a + b r_0 = 0$, and let
$\chi : \mathbb{Z}/\ell \to \mathbb{C}$ be such that for every $t \ne 0$ there is
$j \in \mathbb{N}$ with $\chi(t) = \rho^j$ and $t^{(\ell-1)/3} = r_0^j$. Put
$\Lambda = \varphi(1/\lambda)$ and $\tilde\lambda = \prod \varphi(r/\lambda)$, the product
over the integers $0 < r < \ell$ with $\chi(r) = 1$. Then
$\tilde\lambda^2 - \Lambda^{2(\ell-1)/3} = \Lambda^{2(\ell-1)/3 + 1} x$ for some algebraic
integer $x$ in the subfield $\mathbb{Q}(\rho, \Lambda)$ of $\mathbb{C}$.

Here $\lambda\bar\lambda = \ell$, $\rho \mapsto r_0$ identifies $\mathbb{Z}[\rho]/(\lambda)$ with
$\mathbb{Z}/\ell$, and $\chi$ is the cubic residue character modulo $\lambda$. The statement is
the congruence $\tilde\lambda^2 \equiv \Lambda^{2(\ell-1)/3}$ modulo $\Lambda^{2(\ell-1)/3 + 1}$
in the ring of integers of $\mathbb{Q}(\rho, \Lambda)$.

## Sources

- Akihiro Goto, *Congruence Relations Connecting Tate-Shafarevich Groups with Bernoulli-Hurwitz Numbers by Elliptic Gauss Sums in the Eisenstein Integers Case*, INTEGERS 26 (2026), Article A112, Lemma 10.
