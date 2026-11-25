# Siegel's mass formula for definite Hermitian lattices over a quadratic extension

Let $K$ be a totally real number field of degree $n$, with ring of integers $\mathfrak{o}$ and discriminant of absolute
value $d_K$, let $E/K$ be a totally imaginary quadratic extension, with ring of integers $\mathcal{O}$ and relative
discriminant $\mathfrak{d}_{E/K}$, and let $(V, \Phi)$ be a definite Hermitian space over $E$ of rank $m \ge 1$, with the
[mass, local densities and local factors](hermitian-lattice-mass-and-local-factors.md) of its lattices. For a prime ideal
$\mathfrak{p}$ of $\mathfrak{o}$ let $\chi(\mathfrak{p}) = 1$, $-1$ or $0$ according as $\mathfrak{p}$ splits, is inert or ramifies in $E$,
and for $i \ge 1$ and $\operatorname{Re} s > 1$ let

$$L_K(\chi^i, s) = \prod_{\mathfrak{p}} \bigl(1 - \chi_i(\mathfrak{p}) N\mathfrak{p}^{-s}\bigr)^{-1}, \qquad \chi_i(\mathfrak{p}) = \chi(\mathfrak{p})^i \text{ for odd } i, \quad \chi_i(\mathfrak{p}) = 1 \text{ for even } i,$$

the product running over the prime ideals of $\mathfrak{o}$, so that $L_K(\chi^i, s) = \zeta_K(s)$ for even $i$. For
$\operatorname{Re} s > 1$, $L_K(\chi, s) = \zeta_E(s) / \zeta_K(s)$, and $L_K(\chi, 1)$ denotes the limit of
$\zeta_E(s) / \zeta_K(s)$ as $s \to 1$, the quotient of the residues of the two Dedekind zeta functions at their simple
poles at $s = 1$, which is finite and nonzero.

Then for every $\mathcal{O}$-lattice $L$ in $V$ the genus of $L$ consists of finitely many isometry classes and their
automorphism groups are finite, so that $\mathrm{Mass}(L)$ is defined. If $L$ is integral, then
$\lambda(L_{\mathfrak{p}}) = 1$ for all but finitely many $\mathfrak{p}$, and

$$\mathrm{Mass}(L) = 2 \gamma_m^{-n} \, d_K^{\,m^2/2} \, N_{K/\mathbb{Q}}(\mathfrak{d}_{E/K})^{m(m - (-1)^m)/4} \prod_{i=1}^{m} L_K(\chi^i, i) \prod_{\mathfrak{p}} \lambda(L_{\mathfrak{p}}), \qquad \gamma_m = \prod_{i=1}^{m} \frac{(2\pi)^i}{(i - 1)!},$$

the last product running over the prime ideals of $\mathfrak{o}$.

The identity $L_K(\chi, s) = \zeta_E(s) / \zeta_K(s)$ holds factor by factor in the Euler products of the two Dedekind
zeta functions: for a prime ideal $\mathfrak{p}$ of $\mathfrak{o}$ of norm $q$, the sum of $e f$ over the prime ideals of
$\mathcal{O}$ above $\mathfrak{p}$, with ramification index $e$ and residue degree $f$, is $[E : K] = 2$, by the
[sum of the local degrees](../algebraic-number-theory/discriminants-ramification/completions-of-number-fields-at-finite-places/the-finite-place-completion-tensor-product/sum-finrank-adic-completion-places-over.md)
and [their values $e f$](../algebraic-number-theory/discriminants-ramification/completions-of-number-fields-at-finite-places/finrank-adic-completion-eq-ramification.md),
and a prime ideal of residue degree $f$ has norm $q^f$
([residue cardinality](../../RingTheory/ramification/frobenius-elements/arithmetic-frobenius-in-towers-and-restrictions/nat-card-quotient-under-eq-pow-inertia-d.md));
so the factor of $\zeta_E / \zeta_K$ at $\mathfrak{p}$ is $(1 - q^{-s})^{-1}$, $(1 + q^{-s})^{-1}$ or $1$ according as $\mathfrak{p}$
splits, is inert or ramifies. The local factor $\lambda(L_{\mathfrak{p}})$ is $1$ at every prime $\mathfrak{p}$ that is unramified in
$E$ and at which $L_{\mathfrak{p}}$ is unimodular, by the values at
[split primes](hermitian-unimodular-local-factor-split.md) and at [inert primes](hermitian-unimodular-local-factor-inert.md);
this excludes only finitely many $\mathfrak{p}$, since
[only finitely many primes ramify](../../RingTheory/ramification/different-and-discriminant-ideals/finite-ramified-primes-below.md)
and the finite group $L^\# / L$ is supported at finitely many primes.

Kirschmer obtains this form from Siegel's mass formula in local-density form, his Theorem 4.2.3, which for an
integral $L$ reads
$\mathrm{Mass}(L) = 2 \gamma_m^{-n} d_K^{\,m^2/2} N_{K/\mathbb{Q}}(\mathfrak{d}_{E/K})^{m(m+1)/4} [L^\# : L]_{\mathbb{Z}}^{m/2} \prod_{\mathfrak{p}} \beta(L_{\mathfrak{p}})^{-1}$,
where $[L^\# : L]_{\mathbb{Z}}$ is the order of $L^\# / L$, the factor $2$ is the Tamagawa number of the unitary group
of $(V, \Phi)$, and the product, which does not converge absolutely, stands for
$L_K(\chi, 1) \prod_{\mathfrak{p}} (1 - \chi(\mathfrak{p}) N\mathfrak{p}^{-1}) \beta(L_{\mathfrak{p}})^{-1}$. At the primes unramified in $E$ at
which $L_{\mathfrak{p}}$ is unimodular, the two local pages give
$\beta(L_{\mathfrak{p}}) = \prod_{j=1}^{m} (1 - \chi(\mathfrak{p})^j N\mathfrak{p}^{-j})$, so the factor
$(1 - \chi(\mathfrak{p}) N\mathfrak{p}^{-1}) \beta(L_{\mathfrak{p}})^{-1}$ is $1 + O(N\mathfrak{p}^{-2})$, and this product converges
absolutely by the
[summability of $\sum_{\mathfrak{p}} N\mathfrak{p}^{-2}$](../zeta-l-functions/dirichlet-l-functions/dedekind-zeta-function-and-polar-density/summable-height-one-spectrum-abs-norm-rp.md).
Kirschmer credits Theorem 4.2.3 to Siegel for quadratic forms and to Gan and Yu in general.

This node is still to be broken down. A good expansion has a page for Siegel's mass formula in local-density form
(Kirschmer, Theorem 4.2.3, with the Tamagawa number $2$ of the unitary group and the product of the local densities
read as above); pages for the finiteness of the number of classes in a genus (Theorem 2.4.5) and of the automorphism
groups (Remark 2.4.4(1)); and a page for the passage to the form above (Proposition 4.2.7(3)). That page explains the
choice of $c_{\mathfrak{p}}$: in the notation of Gan, Hanke and Yu it is the normalising factor
$q^{-\dim \overline{H}} \, \# \overline{H}(\mathbb{F}_q)$ of their formula (2.11), for the connected reductive quotient $\overline{H}$ of
the reference group at $\mathfrak{p}$, by the [order of $\mathrm{GL}_m(\mathbb{F}_q)$](../../GroupTheory/linear-groups/card-general-linear-group-finite-field.md) if
$\mathfrak{p}$ splits ($\overline{H} = \mathrm{GL}_m$), the [order of the finite unitary group](finite-unitary-group-order.md) if
$\mathfrak{p}$ is inert ($\overline{H} = \mathrm{U}_m$), and the orders of $\mathrm{SO}_m(\mathbb{F}_q)$ for odd $m$ and of
$\mathrm{Sp}_m(\mathbb{F}_q)$ for even $m$, for which the expansion adds a page, if $\mathfrak{p}$ ramifies.
Writing each $\beta(L_{\mathfrak{p}})^{-1}$ through $\lambda(L_{\mathfrak{p}})$, the powers $q^{-t_{\mathfrak{p}} m/2}$ cancel
$[L^\# : L]_{\mathbb{Z}}^{m/2}$; at a prime $\mathfrak{p}$ unramified in $E$ the factor $c_{\mathfrak{p}}^{-1}$ is the Euler factor of
$\prod_{i=1}^m L_K(\chi^i, i)$ at $\mathfrak{p}$; and at the ramified primes the factors
$c_{\mathfrak{p}}^{-1} = \prod_{j=1}^{\lfloor m/2 \rfloor} (1 - q^{-2j})^{-1}$ give the Euler factors there, while the powers
$q^{-a_{\mathfrak{p}}}$ change the exponent of $N_{K/\mathbb{Q}}(\mathfrak{d}_{E/K})$ from $m(m+1)/4$ to $m(m - (-1)^m)/4$.

A good expansion also extends the displayed formula to every lattice $L$ in $V$. For a positive integer $A$ such that
the rescaled lattice $L^A$, the module $L$ in the definite Hermitian space $(V, A \Phi)$, is integral, the local factors of
$L$ are defined as those of $L^A$. They do not depend on $A$. If an already integral model is rescaled further by a
positive integer $b$, with $k = \operatorname{ord}_{\mathfrak{p}}(b)$, then $t_{\mathfrak{p}}$ grows by $2mk$ and $\beta$ at $\mathfrak{p}$ is
multiplied by $q^{k m^2}$, so that $\lambda$ at $\mathfrak{p}$ is unchanged (Kirschmer, Proposition 4.2.10(3)); and two clearing
integers $A$ and $B$ give the same local factors, as $L^A$ and $L^B$ both compare in this way with the common integral
model $L^{AB}$. Rescaling the form does not change the isometries, so it changes neither the genus, nor its isometry
classes, nor their automorphism groups, hence not the mass. The quotient $L^\# / L$ and the local density
$\beta(L_{\mathfrak{p}})$ are formed only for integral lattices.

## Depends on

- [Mass and local factors of definite Hermitian lattices](hermitian-lattice-mass-and-local-factors.md)
- [Meromorphic continuation of Hecke L-functions](../zeta-l-functions/dirichlet-l-functions/hecke-l-function-meromorphic-continuation.md), for $\zeta_E$ and $\zeta_K$ (trivial character): their Euler products, which give $L_K(\chi^i, s) = \zeta_K(s)$ for even $i$, and their continuation with simple poles at $s = 1$, which defines $L_K(\chi, 1)$
- [Absolute norm of an ideal](../../RingTheory/dedekind-domains/ideal-absolute-norm.md), for $N\mathfrak{p}$ and $N_{K/\mathbb{Q}}(\mathfrak{d}_{E/K})$

## Proof depends on

- [Local degrees sum to the global degree](../algebraic-number-theory/discriminants-ramification/completions-of-number-fields-at-finite-places/the-finite-place-completion-tensor-product/sum-finrank-adic-completion-places-over.md), for the factorization $L_K(\chi, s) = \zeta_E(s) / \zeta_K(s)$
- [The local degree is the product of ramification index and inertia degree](../algebraic-number-theory/discriminants-ramification/completions-of-number-fields-at-finite-places/finrank-adic-completion-eq-ramification.md), for the factorization $L_K(\chi, s) = \zeta_E(s) / \zeta_K(s)$
- [Intermediate residue cardinality as a power of the base residue cardinality](../../RingTheory/ramification/frobenius-elements/arithmetic-frobenius-in-towers-and-restrictions/nat-card-quotient-under-eq-pow-inertia-d.md), for the norms of the primes of $E$
- [Only finitely many primes of the base ramify](../../RingTheory/ramification/different-and-discriminant-ideals/finite-ramified-primes-below.md)
- [Local factor of a unimodular Hermitian lattice at a split prime](hermitian-unimodular-local-factor-split.md)
- [Local factor of a unimodular Hermitian lattice at an inert prime](hermitian-unimodular-local-factor-inert.md)
- [Summability of Dedekind zeta terms for σ > 1](../zeta-l-functions/dirichlet-l-functions/dedekind-zeta-function-and-polar-density/summable-height-one-spectrum-abs-norm-rp.md), for the absolute convergence of the corrected product $\prod_{\mathfrak{p}} (1 - \chi(\mathfrak{p}) N\mathfrak{p}^{-1}) \beta(L_{\mathfrak{p}})^{-1}$
- [Order of the general linear group over a finite field](../../GroupTheory/linear-groups/card-general-linear-group-finite-field.md), in the expansion plan, for $c_{\mathfrak{p}}$ at the split primes
- [Order of the unitary group over a finite field](finite-unitary-group-order.md), in the expansion plan, for $c_{\mathfrak{p}}$ at the inert primes

## Sources

- M. Kirschmer, *Definite quadratic and hermitian forms with small class number*, Habilitationsschrift,
  RWTH Aachen University (2016), <http://www.math.rwth-aachen.de/~Markus.Kirschmer/papers/herm.pdf>:
  Remark 2.4.4(1) and Theorem 2.4.5 (finite automorphism groups, finitely many classes); Chapter 4: Theorems
  4.1.2 (Euler product of $\zeta_F$) and 4.1.4, the definition of $L_K(\chi, s)$ and equation (4.1.1) before
  Corollary 4.1.5, Table 4.1, Definition 4.2.1 (mass), Theorem 4.2.3 (Siegel's mass formula,
  credited to C. L. Siegel, Ann. of Math. 36 (1935) and 38 (1937), for quadratic forms and to W. T. Gan and
  J.-K. Yu, *Group schemes and local densities*, Duke Math. J. 105 (2000), 497–524, Section 10, in general),
  Theorem 4.2.4, Lemma 4.2.5, Definition 4.2.6, Proposition 4.2.7(3) and Proposition 4.2.10(2) and (3) (with
  Definition 2.3.3(9), the rescaled lattice $L^c$, the module $L$ in $(V, c \Phi)$).
- W. T. Gan and J.-K. Yu, *Group schemes and local densities*, Duke Math. J. 105 (2000), 497–524,
  <https://bpb-us-w2.wpmucdn.com/blog.nus.edu.sg/dist/3/12891/files/2020/08/duke-local-density.pdf>, Section 10:
  §§10.7–10.8 (the mass in terms of the local densities, whose product converges only conditionally when the group is
  not semisimple, as for unitary groups) and §10.9 (Tamagawa number $\tau(G) = 2$ for the unitary group of a quadratic extension, the case $K = E$ in Gan and Yu's
  notation of §10.2).
- W. T. Gan, J. P. Hanke and J.-K. Yu, *On an exact mass formula of Shimura*, Duke Math. J. 107 (2001), 103–133,
  <https://www.jonhanke.com/Hanke--all_papers__as_of_2015-01-14/exact-mass-shimura-paper.pdf>: formula (2.11), the
  normalising factor $q^{-\dim \overline{H}^0} \# \overline{H}^0(A/\pi)$ of the connected reductive quotient of the reference
  model, and §3, Tables 1 and 2, its type $\mathrm{SO}_{2n+1}$ (odd rank) and $\mathrm{Sp}_{2n}$ (even rank) at a ramified
  place and $\mathrm{U}_m$ at an unramified one.
