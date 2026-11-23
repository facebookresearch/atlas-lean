# Local factor of a unimodular Hermitian lattice at an inert prime

Let $K$, $E$, $\mathfrak{o}$, $\mathcal{O}$ and the definite Hermitian space $(V, \Phi)$ of rank $m$ be as in
[Mass and local factors of definite Hermitian lattices](hermitian-lattice-mass-and-local-factors.md), let $\mathfrak{p}$ be a
prime ideal of $\mathfrak{o}$ of norm $q$ that is inert in $E$, and let $L$ be an integral $\mathcal{O}$-lattice in $V$ with
$L_{\mathfrak{p}}$ unimodular. Then the local density and the local factor of $L$ at $\mathfrak{p}$ are

$$\beta(L_{\mathfrak{p}}) = q^{-m^2} \, \# \mathrm{U}_m(\mathbb{F}_q) = \prod_{j=1}^{m} \bigl(1 - (-q)^{-j}\bigr), \qquad \lambda(L_{\mathfrak{p}}) = 1,$$

where $\mathrm{U}_m(\mathbb{F}_q)$ is the unitary group of a nondegenerate Hermitian form in $m$ variables over $\mathbb{F}_{q^2}$.

Indeed $\mathfrak{p}$ has one prime ideal of $\mathcal{O}$ above it, with ramification index $1$ and residue degree $2$, so the
[base change to the completion](../algebraic-number-theory/discriminants-ramification/completions-of-number-fields-at-finite-places/the-finite-place-completion-tensor-product/completion-tensor-product-alg-equiv.md) is a field $E_{\mathfrak{p}}$ of [degree $e f = 2$](../algebraic-number-theory/discriminants-ramification/completions-of-number-fields-at-finite-places/finrank-adic-completion-eq-ramification.md) over $K_{\mathfrak{p}}$, and
$\mathcal{O}_{\mathfrak{p}}$ is the unramified quadratic extension of $\mathfrak{o}_{\mathfrak{p}}$, with residue field $\mathbb{F}_{q^2}$ and a
uniformizer $\pi \in \mathfrak{o}_{\mathfrak{p}}$. The lattice $L_{\mathfrak{p}}$ is free with an invertible Hermitian Gram matrix $G$,
so $H(R) = \{g : g^* G g = G\}$ in the definition of $\beta(L_{\mathfrak{p}})$, and $H(\mathfrak{o}/\mathfrak{p})$ is the unitary group of
the nondegenerate Hermitian space $L_{\mathfrak{p}} / \pi L_{\mathfrak{p}}$ over $\mathbb{F}_{q^2}$. For $N \ge 1$ every
$h \in H(\mathfrak{o}/\mathfrak{p}^N)$ lifts, and its lifts to $H(\mathfrak{o}/\mathfrak{p}^{N+1})$ form one coset of a group of order
$q^{m^2}$: if $g$ lifts $h$ to a matrix with $g^* G g = G + \pi^N Y$, the lifts $g(1 + \pi^N X)$ lie in $H$ exactly when
$(GX)^* + GX \equiv -Y \pmod{\pi}$, and $Z \mapsto Z^* + Z$ maps the $m \times m$ matrices over $\mathbb{F}_{q^2}$ onto the
Hermitian ones, because the trace of $\mathbb{F}_{q^2}/\mathbb{F}_q$ is onto, with the $q^{m^2}$ skew-Hermitian matrices as
kernel. So $\# H(\mathfrak{o}/\mathfrak{p}^N) = q^{(N-1) m^2} \# \mathrm{U}_m(\mathbb{F}_q)$ and
$\beta(L_{\mathfrak{p}}) = q^{-m^2} \# \mathrm{U}_m(\mathbb{F}_q)$, which is $\prod_{j=1}^{m} (1 - (-q)^{-j})$ by the
[order of the finite unitary group](finite-unitary-group-order.md). In the definition of $\lambda(L_{\mathfrak{p}})$,
$t_{\mathfrak{p}} = 0$, $a_{\mathfrak{p}} = 0$ and $c_{\mathfrak{p}} = \prod_{j=1}^{m} (1 - (-q)^{-j}) = \beta(L_{\mathfrak{p}})$, so
$\lambda(L_{\mathfrak{p}}) = 1$.

The prime $\mathfrak{p}$ is good in Kirschmer's sense, and these values are his Theorem 4.2.4 (after Gan and Yu) for the
Jordan decomposition $L_{\mathfrak{p}} = L_1$ with $s_1 = 0$, where $N = 0$ and $G_1 = \mathrm{U}_m$, and the inert row of his
Lemma 4.2.9 with $m_0 = m$, where $\lambda(L_{\mathfrak{p}}) = \bigl|\binom{m}{m}_{-q}\bigr| = 1$.

## Depends on

- [Mass and local factors of definite Hermitian lattices](hermitian-lattice-mass-and-local-factors.md), for $\beta(L_{\mathfrak{p}})$ and $\lambda(L_{\mathfrak{p}})$

## Proof depends on

- [Base change to a finite completion as a product of completions](../algebraic-number-theory/discriminants-ramification/completions-of-number-fields-at-finite-places/the-finite-place-completion-tensor-product/completion-tensor-product-alg-equiv.md)
- [The local degree is the product of ramification index and inertia degree](../algebraic-number-theory/discriminants-ramification/completions-of-number-fields-at-finite-places/finrank-adic-completion-eq-ramification.md)
- [Order of the unitary group over a finite field](finite-unitary-group-order.md)

## Sources

- M. Kirschmer, *Definite quadratic and hermitian forms with small class number*, Habilitationsschrift,
  RWTH Aachen University (2016), <http://www.math.rwth-aachen.de/~Markus.Kirschmer/papers/herm.pdf>:
  Definition 3.5.1 (good prime ideals); Section 4.2: Definition 4.2.2, Theorem 4.2.4 (citing W. T. Gan and
  J.-K. Yu, *Group schemes and local densities*, Duke Math. J. 105 (2000), 497–524, Theorem 7.3), Lemma 4.2.5
  (inert row: $d = 2$, $G_i = \mathrm{U}_{m_i}$), the table of $\# \mathrm{U}_m(\mathbb{F}_q)$ after it, Definition 4.2.6,
  Definition 4.2.8 (Gaussian binomial coefficients) and Lemma 4.2.9 (row $\dim_K E = 2$,
  $E_{\mathfrak{p}}/K_{\mathfrak{p}}$ inert).
- W. T. Gan and J.-K. Yu, *Group schemes and local densities*, Duke Math. J. 105 (2000), 497–524,
  <https://bpb-us-w2.wpmucdn.com/blog.nus.edu.sg/dist/3/12891/files/2020/08/duke-local-density.pdf>: Theorem 7.3 and
  §9.3, which states that this local density formula remains valid in residue characteristic $2$ for Hermitian spaces over
  $F \oplus F$ and over an unramified quadratic extension of $F$.
