# Unique identification of the final-size PGF of a multi-type Galton–Watson process

**Setting.** A multi-type Galton–Watson process with $n$ types models transmission chains in which an infected individual of type $i$ produces offspring counts $X^{(i)} = (X_{i1}, \dots, X_{in}) \in \mathbb{N}_0^n$ with probability generating function $G^{(i)}(z) = \mathbb{E}\big[\prod_j z_j^{X_{ij}}\big]$, $z \in \mathbb{C}^n$. Write $G = (G^{(1)}, \dots, G^{(n)})$, assume the mean offspring matrix $K = [\partial G^{(i)}/\partial z_j(\mathbf{1})]$ is finite and irreducible and the process is nonsingular, and let $q \in [0,1]^n$ be the extinction-probability vector, the smallest nonnegative solution of $q = G(q)$. For a process started from one type-$i$ individual with extinction generation $\tau$, the finite final size $Y^{(i)} = \sum_{m=0}^{\tau - 1} Z_m^{(i)}$ (total infections by type) has the defective PGF

$$

H^{(i)}(z) = \mathbb{E}_i\big[z^{Y};\ \tau < \infty\big] = \sum_{d \in \mathbb{N}_0^n} \mathbb{P}_i(Y = d,\ \tau < \infty)\, z^{d}, \qquad H(\mathbf{1}) = q,

$$

which satisfies the final-size equation $H(z) = z \odot G(H(z))$ ($\odot$ is the componentwise product; inequalities and moduli of vectors are componentwise).

**Theorem (unique identification).** For every $z \in \mathbb{C}^n$ with $|z| < \mathbf{1}$, the fixed-point equation

$$

h = T_z(h) := z \odot G(h)

$$

has exactly one solution $h^*(z)$ in the closed unit polydisc $\{h \in \mathbb{C}^n : |h| \le \mathbf{1}\}$; it equals $H(z)$ and satisfies $|h^*(z)| \le |z| \odot q$. The statement holds for subcritical, critical and supercritical processes alike, so any root found in the polydisc may be used in Cauchy coefficient extraction of the final-size distribution on a contour inside the unit polydisc.

**Corollary (Picard error bound).** Let $|z| < \mathbf{1}$, $r_{\max} = \max_j |z_j|$ and $|u| \le \mathbf{1}$. Then for every type $i$,

$$

\big|(T_z^{\circ m}(u))^{(i)} - H^{(i)}(z)\big| \le 2\,r_{\max}^m, \qquad \big|(T_z^{\circ m}(\mathbf{0}))^{(i)} - H^{(i)}(z)\big| \le r_{\max}^m.

$$

Moreover $T_z$ maps $\mathcal{D}_z = \{h : |h| \le |z| \odot q\}$ into itself and is a contraction there for a suitable weighted sup-norm. If $G(\cdot\,; \theta)$ depends smoothly ($C^s$) on parameters $\theta$, then $H(z; \theta)$ and each final-size probability $[z^d]H^{(i)}(z; \theta)$ are $C^s$ in $\theta$.

## Depends on

- [Comparison principle for Galton–Watson extinction](../superspreading-and-negative-binomial-offspring/extinction-prob-le-of-pgf-le.md)

## Expansion

Iterating $T_z$ is tree extension: $(T_z^{\circ m}(u))^{(i)} = \mathbb{E}_i[z^{S_{m-1}} u^{Z_m}]$, where $S_{m-1}$ counts all individuals before generation $m$ and $u$ marks generation $m$. Two starting points $x, y$ in the polydisc give iterates that differ only on trees still alive at generation $m$; each such tree contains at least $m$ individuals, which carry a factor of modulus at most $r_{\max}^m$, so the difference is at most $2 r_{\max}^m$. Hence every fixed point in the polydisc coincides with the limit $H(z)$, which gives uniqueness and the Picard bound. The bound $|H(z)| \le |z| \odot q$ follows because every finite tree has at least its root, contributing a factor $|z_i|$, and its total probability is $q^{(i)}$. Parameter differentiability follows from uniform convergence of the iterates. Likelihoods for outbreak sizes that are not conditioned on extinction can therefore be computed directly from offspring PGFs such as negative multinomial laws.

## Sources

- Yuta Okada, Hiroshi Nishiura, *Computing the final epidemic size distributions of a multi-type Galton–Watson process*, arXiv 2026. Section 3 (main theorem on unique identification of the final-size PGF), Section 4.1 (corollary: error bound for Picard iteration), Section 4.2 (lemma: contraction on $\mathcal{D}_z$), Section 4.3 (corollary: parameter differentiability). <https://doi.org/10.48550/arXiv.2606.03007>
