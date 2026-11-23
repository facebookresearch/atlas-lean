# Siegel's mass formula for definite Hermitian lattices over a quadratic extension

Let $K$ be a totally real number field of degree $n$, with ring of integers $\mathfrak{o}$ and discriminant of absolute
value $d_K$, and let $E/K$ be a totally imaginary quadratic extension, with ring of integers $\mathcal{O}$, nontrivial
automorphism $x \mapsto \bar{x}$, relative discriminant $\mathfrak{d}_{E/K}$ (the discriminant ideal of $\mathcal{O}$ over
$\mathfrak{o}$) and nontrivial character $\chi$ of $\mathrm{Gal}(E/K)$. Let $(V, \Phi)$ be a definite Hermitian space over $E$
of rank $m \ge 1$, as in the [local–global principle](hermitian-local-global-principle.md): $V$ is an $E$-vector space of
dimension $m$ and $\Phi \colon V \times V \to E$ is additive in each variable, with
$\Phi(\alpha x, \beta y) = \alpha \Phi(x, y) \bar{\beta}$ and $\Phi(y, x) = \overline{\Phi(x, y)}$, and definite means that
$\Phi(x, x)$, which lies in $K$, is totally positive for every nonzero $x \in V$. An $\mathcal{O}$-lattice in $V$ is a finitely
generated $\mathcal{O}$-submodule $L$ that contains an $E$-basis of $V$; its dual is
$L^\# = \{x \in V : \Phi(x, L) \subseteq \mathcal{O}\}$, and $L$ is integral if $L \subseteq L^\#$ and unimodular if
$L = L^\#$. The genus of $L$ is the set of $\mathcal{O}$-lattices $L'$ in $V$ whose completions $L'_{\mathfrak{p}}$ are
isometric to $L_{\mathfrak{p}}$ at every prime ideal $\mathfrak{p}$ of $\mathfrak{o}$; it is the disjoint union of finitely many
isometry classes, represented by $L_1, \dots, L_h$, and the groups $\mathrm{Aut}(L_i)$ of isometries of $(V, \Phi)$ mapping
$L_i$ onto itself are finite. The mass of $L$ is

$$\mathrm{Mass}(L) = \sum_{i=1}^{h} \frac{1}{\# \mathrm{Aut}(L_i)}.$$

For an integral $L$ and a prime ideal $\mathfrak{p}$ of $\mathfrak{o}$ of norm $q$, let $H(R)$ be the set of
$\mathcal{O}_{\mathfrak{p}} \otimes R$-linear endomorphisms $\varphi$ of $L_{\mathfrak{p}} \otimes R$ with
$\Phi(\varphi x, \varphi y) = \Phi(x, y)$, for every commutative $\mathfrak{o}_{\mathfrak{p}}$-algebra $R$. The local density
of $L$ at $\mathfrak{p}$ is

$$\beta(L_{\mathfrak{p}}) = \lim_{N \to \infty} \frac{\# H(\mathfrak{o}/\mathfrak{p}^N)}{q^{N m^2}},$$

$m^2$ being the dimension of the unitary group of $(V, \Phi)$, which is connected. The local factor of $L$ at $\mathfrak{p}$
is

$$\lambda(L_{\mathfrak{p}}) = q^{\operatorname{ord}_{\mathfrak{p}}([L^\#_{\mathfrak{p}} : L_{\mathfrak{p}}]) \, m/2 + a_{\mathfrak{p}}} \cdot \frac{q^{-\dim H_{\mathfrak{p}}} \cdot \# H_{\mathfrak{p}}(\mathfrak{o}/\mathfrak{p})}{[H_{\mathfrak{p}} : H_{\mathfrak{p}}^0] \cdot \beta(L_{\mathfrak{p}})},$$

where $[L^\#_{\mathfrak{p}} : L_{\mathfrak{p}}]$ is the index ideal of $\mathfrak{o}_{\mathfrak{p}}$, $a_{\mathfrak{p}} = \operatorname{ord}_{\mathfrak{p}}(\mathfrak{d}_{E/K}) \, m/2$
if $\mathfrak{p}$ ramifies in $E$ and $m$ is even and $a_{\mathfrak{p}} = 0$ otherwise, and $\dim H_{\mathfrak{p}}$,
$\# H_{\mathfrak{p}}(\mathfrak{o}/\mathfrak{p})$ and $[H_{\mathfrak{p}} : H_{\mathfrak{p}}^0]$ are the dimension, the number of points and the
number of connected components of the group over $\mathbb{F}_q = \mathfrak{o}/\mathfrak{p}$ that Kirschmer's table, after Gan,
Hanke and Yu, attaches at $\mathfrak{p}$ to the quasi-split inner form $H_{\mathfrak{p}}$ of the unitary group: $\mathrm{GL}_m$ if
$\mathfrak{p}$ splits in $E$, the unitary group $\mathrm{U}_m$ of a nondegenerate Hermitian form over $\mathbb{F}_{q^2}$ if
$\mathfrak{p}$ is inert, $\mathrm{O}_m$ if $\mathfrak{p}$ ramifies and $m$ is odd, and $\mathrm{Sp}_m$ if $\mathfrak{p}$ ramifies and $m$ is
even. Then $\lambda(L_{\mathfrak{p}}) = 1$ for all but finitely many $\mathfrak{p}$, and

$$\mathrm{Mass}(L) = 2 \gamma_m^{-n} \, d_K^{\,m^2/2} \, N_{K/\mathbb{Q}}(\mathfrak{d}_{E/K})^{m(m - (-1)^m)/4} \prod_{i=1}^{m} L_K(\chi^i, i) \prod_{\mathfrak{p}} \lambda(L_{\mathfrak{p}}), \qquad \gamma_m = \prod_{i=1}^{m} \frac{(2\pi)^i}{(i - 1)!},$$

the last product running over the prime ideals of $\mathfrak{o}$. Here, for $\operatorname{Re} s > 1$,
$L_K(\chi^i, s) = \prod_{\mathfrak{p}} (1 - \chi^i(\mathfrak{p}) N\mathfrak{p}^{-s})^{-1}$, with $\chi(\mathfrak{p}) = 1$, $-1$ or $0$
according as $\mathfrak{p}$ splits, is inert or ramifies in $E$ and with $\chi^i = 1$ for even $i$, so that
$L_K(\chi^i, s) = \zeta_K(s)$ for even $i$ and $L_K(\chi, s) = \zeta_E(s) / \zeta_K(s)$; the value $L_K(\chi, 1)$ is that of the
meromorphic continuation of $\zeta_E / \zeta_K$, the quotient of the residues of $\zeta_E$ and $\zeta_K$ at $s = 1$, so it is
finite and nonzero. Since scaling $\Phi$ by an element of $K^\times$ changes neither the mass nor the local factors, the
formula, stated for integral $L$, extends to every $\mathcal{O}$-lattice.

Kirschmer obtains this form from Siegel's mass formula in local-density form, his Theorem 4.2.3, which for an
integral $L$ reads
$\mathrm{Mass}(L) = 2 \gamma_m^{-n} d_K^{\,m^2/2} N_{K/\mathbb{Q}}(\mathfrak{d}_{E/K})^{m(m+1)/4} [L^\# : L]_{\mathbb{Z}}^{m/2} \prod_{\mathfrak{p}} \beta(L_{\mathfrak{p}})^{-1}$,
where $[L^\# : L]_{\mathbb{Z}}$ is the order of $L^\# / L$, the factor $2$ is the Tamagawa number of the unitary group
of $(V, \Phi)$, and the product, which does not converge absolutely, stands for
$L_K(\chi, 1) \prod_{\mathfrak{p}} (1 - \chi(\mathfrak{p}) N\mathfrak{p}^{-1}) \beta(L_{\mathfrak{p}})^{-1}$; he credits it to Siegel in the
quadratic case and to Gan and Yu in general.

This node is still to be broken down. A good expansion has a page for Siegel's mass formula in local-density form
(Kirschmer, Theorem 4.2.3, with the Tamagawa number $2$ of the unitary group and the product of the local densities
read as above: at the primes $\mathfrak{p}$ unramified in $E$ at which $L_{\mathfrak{p}}$ is unimodular, all but finitely
many, $\beta(L_{\mathfrak{p}}) = \prod_{i=1}^{m} (1 - \chi(\mathfrak{p})^i N\mathfrak{p}^{-i})$ (Theorem 4.2.4 and Lemma 4.2.5), so the
factor $(1 - \chi(\mathfrak{p}) N\mathfrak{p}^{-1}) \beta(L_{\mathfrak{p}})^{-1}$ is $1 + O(N\mathfrak{p}^{-2})$, and the product converges
absolutely by the
[summability of $\sum_{\mathfrak{p}} N\mathfrak{p}^{-2}$](../zeta-l-functions/dirichlet-l-functions/dedekind-zeta-function-and-polar-density/summable-height-one-spectrum-abs-norm-rp.md)); pages for the facts that make the
statement meaningful: the finiteness of the number of classes in a genus (Kirschmer, Theorem 2.4.5) and of the
automorphism groups (Remark 2.4.4(1)), the finiteness of the set of $\mathfrak{p}$ with $\lambda(L_{\mathfrak{p}}) \neq 1$
(Proposition 4.2.10(2), from Lemma 4.2.9), and the invariance of the mass and of the local factors under scaling
(after Definition 4.2.1, and Proposition 4.2.10(3)); and a page for the passage to the form above (Proposition
4.2.7(3)). Writing each $\beta(L_{\mathfrak{p}})^{-1}$ through $\lambda(L_{\mathfrak{p}})$, the powers
$q^{-\operatorname{ord}_{\mathfrak{p}}([L^\#_{\mathfrak{p}} : L_{\mathfrak{p}}]) m/2}$ cancel $[L^\# : L]_{\mathbb{Z}}^{m/2}$; at a prime
$\mathfrak{p}$ unramified in $E$ the factor
$q^{\dim H_{\mathfrak{p}}} / \# H_{\mathfrak{p}}(\mathfrak{o}/\mathfrak{p}) = \prod_{i=1}^{m} (1 - \chi(\mathfrak{p})^i q^{-i})^{-1}$ is the Euler
factor of $\prod_{i=1}^m L_K(\chi^i, i)$ at $\mathfrak{p}$; and at the ramified primes the factors
$[H_{\mathfrak{p}} : H_{\mathfrak{p}}^0] \, q^{\dim H_{\mathfrak{p}}} / \# H_{\mathfrak{p}}(\mathfrak{o}/\mathfrak{p}) = \prod_{j=1}^{\lfloor m/2 \rfloor} (1 - q^{-2j})^{-1}$
give the Euler factors there, while the powers $q^{-a_{\mathfrak{p}}}$ change the exponent of $N_{K/\mathbb{Q}}(\mathfrak{d}_{E/K})$
from $m(m+1)/4$ to $m(m - (-1)^m)/4$.

## Depends on

- [Discriminant ideal of a Dedekind extension](../../RingTheory/ramification/different-and-discriminant-ideals/discriminant-ideal.md), for the relative discriminant $\mathfrak{d}_{E/K}$
- [Meromorphic continuation of Hecke L-functions](../zeta-l-functions/dirichlet-l-functions/hecke-l-function-meromorphic-continuation.md), for the continuation of $\zeta_E$ and $\zeta_K$ (trivial character), which defines $L_K(\chi, 1)$

## Sources

- M. Kirschmer, *Definite quadratic and hermitian forms with small class number*, Habilitationsschrift,
  RWTH Aachen University (2016), <http://www.math.rwth-aachen.de/~Markus.Kirschmer/papers/herm.pdf>:
  Definitions 2.1.1–2.1.3 (Hermitian spaces), 2.2.2, 2.3.3 and 2.3.5, item 1 of Section 2.4 (definite spaces),
  Definition 2.4.2 (genus), Remark 2.4.4(1) and Theorem 2.4.5 (finite automorphism groups, finitely many classes);
  Chapter 4: the relative discriminant $\mathfrak{d}_{E/K} = N(\mathfrak{D})$ at the start of the chapter, Theorems 4.1.2
  and 4.1.4, the definition of $L_K(\chi, s)$ and equation (4.1.1) before Corollary 4.1.5, Table 4.1, Definition 4.2.1
  (mass) and the remark after it, Definition 4.2.2 (local density), Theorem 4.2.3 (Siegel's mass formula, credited to
  C. L. Siegel, Ann. of Math. 36 (1935) and 38 (1937), in the quadratic case and to W. T. Gan and J.-K. Yu,
  *Group schemes and local densities*, Duke Math. J. 105 (2000), 497–524, Section 10, in general), the table of
  dimensions and numbers of points after Lemma 4.2.5, Definition 4.2.6 (local factors) and the table of
  $H_{\mathfrak{p}}$ after it (after W. T. Gan, J. Hanke and J.-K. Yu, Duke Math. J. 107 (2001)), Proposition 4.2.7(3)
  and Proposition 4.2.10(2) and (3).
