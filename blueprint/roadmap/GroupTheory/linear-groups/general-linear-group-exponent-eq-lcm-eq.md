# Exponent of the general linear group over a prime field

Let $p$ be a prime and let
$m \ge 1$. The exponent of the group $\mathrm{GL}_m(\mathbb{F}_p)$ of invertible $m \times m$
matrices over $\mathbb{F}_p = \mathbb{Z}/p\mathbb{Z}$ is

$$p^{\lceil \log_p m \rceil} \cdot \operatorname{lcm}(p - 1, p^2 - 1, \dots, p^m - 1),$$

and this number equals $p^{\lceil \log_p m \rceil} \prod_{k=1}^{m} \Phi_k(p)$, where $\Phi_k$
denotes the $k$-th cyclotomic polynomial.

## Sources

- Eugene Karolinsky and Dmytro Seliutin, *Carmichael Numbers for GL(m)*, Journal of Integer Sequences 23 (2020), Article 20.10.6, <https://cs.uwaterloo.ca/journals/JIS/VOL23/Karolinsky/kar2.tex>, Theorem `fermat_matr` (quoting J. B. Marshall, *On the extension of Fermat's theorem to matrices of order n*, Proc. Edinb. Math. Soc. 6 (1939), and I. Niven, *Fermat's theorem for matrices*, Duke Math. J. 15 (1948)), lines 139-144; the lcm/cyclotomic identity is the paper's Proposition, lines 113-118.
