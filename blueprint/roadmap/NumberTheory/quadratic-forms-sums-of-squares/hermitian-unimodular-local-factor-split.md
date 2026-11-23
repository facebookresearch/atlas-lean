# Local factor of a unimodular Hermitian lattice at a split prime

Let $K$, $E$, $\mathfrak{o}$, $\mathcal{O}$ and the definite Hermitian space $(V, \Phi)$ of rank $m$ be as in
[Mass and local factors of definite Hermitian lattices](hermitian-lattice-mass-and-local-factors.md), let $\mathfrak{p}$ be a
prime ideal of $\mathfrak{o}$ of norm $q$ that splits in $E$, and let $L$ be an integral $\mathcal{O}$-lattice in $V$ with
$L_{\mathfrak{p}}$ unimodular. Then the local density and the local factor of $L$ at $\mathfrak{p}$ are

$$\beta(L_{\mathfrak{p}}) = q^{-m^2} \, \# \mathrm{GL}_m(\mathbb{F}_q) = \prod_{j=1}^{m} (1 - q^{-j}), \qquad \lambda(L_{\mathfrak{p}}) = 1.$$

Indeed $\mathcal{O}$ is a finitely generated $\mathfrak{o}$-module, so $\mathcal{O}_{\mathfrak{p}} = \mathcal{O} \otimes_{\mathfrak{o}} \mathfrak{o}_{\mathfrak{p}}$ is
the $\mathfrak{p}$-adic completion $\varprojlim_N \mathcal{O}/\mathfrak{p}^N \mathcal{O}$, which by the factorization of $\mathfrak{p}\mathcal{O}$ and
the Chinese remainder theorem is the product of the completions $\widehat{\mathcal{O}}_{\mathfrak{P}}$ over the prime ideals
$\mathfrak{P}$ of $\mathcal{O}$ above $\mathfrak{p}$. Here there are two of them, each with ramification index and residue degree $1$, so
each completion $E_{\mathfrak{P}}$ has [degree $e f = 1$](../algebraic-number-theory/discriminants-ramification/completions-of-number-fields-at-finite-places/finrank-adic-completion-eq-ramification.md) over $K_{\mathfrak{p}}$ and
$\widehat{\mathcal{O}}_{\mathfrak{P}} = \mathfrak{o}_{\mathfrak{p}}$; thus $\mathcal{O}_{\mathfrak{p}} = \mathfrak{o}_{\mathfrak{p}} \times \mathfrak{o}_{\mathfrak{p}}$, with the
involution exchanging the factors. So $L_{\mathfrak{p}} = A \oplus A'$ for free $\mathfrak{o}_{\mathfrak{p}}$-modules $A$, $A'$ of rank $m$,
and $\Phi$ is given by a pairing of $A$ with $A'$, perfect because $L_{\mathfrak{p}}$ is unimodular. An isometry of
$L_{\mathfrak{p}} \otimes R$ is determined by its restriction to $A \otimes R$, which can be any automorphism, so the set
$H(R)$ of the definition of $\beta(L_{\mathfrak{p}})$ is $\mathrm{GL}_m(R)$. The reduction map
$\mathrm{GL}_m(\mathfrak{o}/\mathfrak{p}^N) \to \mathrm{GL}_m(\mathbb{F}_q)$ is onto, with kernel $1 + \mathfrak{p} M_m(\mathfrak{o}/\mathfrak{p}^N)$
of order $q^{(N - 1) m^2}$, so $\# H(\mathfrak{o}/\mathfrak{p}^N) = q^{(N-1) m^2} \# \mathrm{GL}_m(\mathbb{F}_q)$ and
$\beta(L_{\mathfrak{p}}) = q^{-m^2} \# \mathrm{GL}_m(\mathbb{F}_q)$, where
$\# \mathrm{GL}_m(\mathbb{F}_q) = q^{m(m-1)/2} \prod_{j=1}^{m} (q^j - 1)$. In the definition of $\lambda(L_{\mathfrak{p}})$,
$t_{\mathfrak{p}} = 0$, $a_{\mathfrak{p}} = 0$ and $c_{\mathfrak{p}} = \prod_{j=1}^{m} (1 - q^{-j}) = \beta(L_{\mathfrak{p}})$, so
$\lambda(L_{\mathfrak{p}}) = 1$.

The prime $\mathfrak{p}$ is good in Kirschmer's sense, and these values are his Theorem 4.2.4 (after Gan and Yu) for the
Jordan decomposition $L_{\mathfrak{p}} = L_1$ with $s_1 = 0$, where $N = 0$ and $G_1 = \mathrm{GL}_m$, and the split row of his
Lemma 4.2.9 with $m_0 = m$, where $\lambda(L_{\mathfrak{p}}) = \binom{m}{m}_q = 1$.

## Depends on

- [Mass and local factors of definite Hermitian lattices](hermitian-lattice-mass-and-local-factors.md), for $\beta(L_{\mathfrak{p}})$ and $\lambda(L_{\mathfrak{p}})$

## Proof depends on

- [The local degree is the product of ramification index and inertia degree](../algebraic-number-theory/discriminants-ramification/completions-of-number-fields-at-finite-places/finrank-adic-completion-eq-ramification.md), for $\widehat{\mathcal{O}}_{\mathfrak{P}} = \mathfrak{o}_{\mathfrak{p}}$

## Sources

- M. Kirschmer, *Definite quadratic and hermitian forms with small class number*, Habilitationsschrift,
  RWTH Aachen University (2016), <http://www.math.rwth-aachen.de/~Markus.Kirschmer/papers/herm.pdf>:
  Definition 3.5.1 (good prime ideals); Section 4.2: Definition 4.2.2, Theorem 4.2.4 (citing W. T. Gan and
  J.-K. Yu, *Group schemes and local densities*, Duke Math. J. 105 (2000), 497–524, Theorem 7.3), Lemma 4.2.5
  (split row: $d = 2$, $G_i = \mathrm{GL}_{m_i}$), the table of $\# \mathrm{GL}_m(\mathbb{F}_q)$ after it, Definition 4.2.6,
  Definition 4.2.8 (Gaussian binomial coefficients) and Lemma 4.2.9 (row $\dim_K E = 2$,
  $E_{\mathfrak{p}}/K_{\mathfrak{p}}$ split).
- W. T. Gan and J.-K. Yu, *Group schemes and local densities*, Duke Math. J. 105 (2000), 497–524,
  <https://bpb-us-w2.wpmucdn.com/blog.nus.edu.sg/dist/3/12891/files/2020/08/duke-local-density.pdf>: Theorem 7.3 and
  §9.3, which states that this local density formula remains valid in residue characteristic $2$ for Hermitian spaces over
  $F \oplus F$ and over an unramified quadratic extension of $F$.
