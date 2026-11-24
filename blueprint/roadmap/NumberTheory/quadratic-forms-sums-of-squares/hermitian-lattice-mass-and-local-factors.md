# Mass and local factors of definite Hermitian lattices

Let $K$ be a totally real number field, with ring of integers $\mathfrak{o}$, and let $E/K$ be a totally imaginary quadratic
extension, with ring of integers $\mathcal{O}$, nontrivial automorphism $x \mapsto \bar{x}$ and relative discriminant
$\mathfrak{d}_{E/K}$, the discriminant ideal of $\mathcal{O}$ over $\mathfrak{o}$. A Hermitian space over $E$ of rank $m \ge 1$
is an $E$-vector space $V$ of dimension $m$ with a map $\Phi \colon V \times V \to E$, additive in each variable, such that
$\Phi(\alpha x, \beta y) = \alpha \Phi(x, y) \bar{\beta}$ and $\Phi(y, x) = \overline{\Phi(x, y)}$; it is definite if
$\Phi(x, x)$, which lies in $K$, is totally positive for every nonzero $x \in V$.

Let $(V, \Phi)$ be a definite Hermitian space over $E$ of rank $m$. An $\mathcal{O}$-lattice in $V$ is a finitely generated
$\mathcal{O}$-submodule $L$ that contains an $E$-basis of $V$; its dual is $L^\# = \{x \in V : \Phi(x, L) \subseteq \mathcal{O}\}$,
and $L$ is integral if $L \subseteq L^\#$ and unimodular if $L = L^\#$. For a prime ideal $\mathfrak{p}$ of $\mathfrak{o}$, $L_{\mathfrak{p}}$
is the completion of $L$ at $\mathfrak{p}$, a lattice over $\mathcal{O}_{\mathfrak{p}} = \mathcal{O} \otimes_{\mathfrak{o}} \mathfrak{o}_{\mathfrak{p}}$, and
$L_{\mathfrak{p}}$ is unimodular if $L^\#_{\mathfrak{p}} = L_{\mathfrak{p}}$.

**Mass.** The genus of $L$ is the set of $\mathcal{O}$-lattices $L'$ in $V$ with $L'_{\mathfrak{p}}$ isometric to $L_{\mathfrak{p}}$ for
every prime ideal $\mathfrak{p}$ of $\mathfrak{o}$; it is a union of isometry classes. Let $\mathrm{Aut}(L')$ be the group of
isometries of $(V, \Phi)$ mapping $L'$ onto itself. If the genus of $L$ consists of finitely many isometry classes,
represented by $L_1, \dots, L_h$, and the groups $\mathrm{Aut}(L_i)$ are finite, the mass of $L$ is

$$\mathrm{Mass}(L) = \sum_{i=1}^{h} \frac{1}{\# \mathrm{Aut}(L_i)}.$$

**Local densities.** Let $L$ be integral and let $\mathfrak{p}$ be a prime ideal of $\mathfrak{o}$ of norm $q$. For every
commutative $\mathfrak{o}_{\mathfrak{p}}$-algebra $R$ let $H(R)$ be the set of $\mathcal{O}_{\mathfrak{p}} \otimes R$-linear endomorphisms
$\varphi$ of $L_{\mathfrak{p}} \otimes R$ with $\Phi(\varphi x, \varphi y) = \Phi(x, y)$. The local density of $L$ at $\mathfrak{p}$ is

$$\beta(L_{\mathfrak{p}}) = \lim_{N \to \infty} \frac{\# H(\mathfrak{o}/\mathfrak{p}^N)}{q^{N m^2}}.$$

**Local factors.** The reference coefficient at $\mathfrak{p}$ is

$$c_{\mathfrak{p}} = \prod_{j=1}^{m} (1 - q^{-j}) \text{ if } \mathfrak{p} \text{ splits in } E, \qquad c_{\mathfrak{p}} = \prod_{j=1}^{m} \bigl(1 - (-q)^{-j}\bigr) \text{ if } \mathfrak{p} \text{ is inert}, \qquad c_{\mathfrak{p}} = \prod_{j=1}^{\lfloor m/2 \rfloor} (1 - q^{-2j}) \text{ if } \mathfrak{p} \text{ ramifies}.$$

Let $t_{\mathfrak{p}}$ be the length of the $\mathfrak{o}_{\mathfrak{p}}$-module $L^\#_{\mathfrak{p}} / L_{\mathfrak{p}}$, and let
$a_{\mathfrak{p}} = \operatorname{ord}_{\mathfrak{p}}(\mathfrak{d}_{E/K}) \, m/2$ if $\mathfrak{p}$ ramifies in $E$ and $m$ is even and $a_{\mathfrak{p}} = 0$
otherwise. The local factor of $L$ at $\mathfrak{p}$ is

$$\lambda(L_{\mathfrak{p}}) = \frac{q^{t_{\mathfrak{p}} m/2 + a_{\mathfrak{p}}} \, c_{\mathfrak{p}}}{\beta(L_{\mathfrak{p}})}.$$

## Depends on

- [Discriminant ideal of a Dedekind extension](../../RingTheory/ramification/different-and-discriminant-ideals/discriminant-ideal.md), for the relative discriminant $\mathfrak{d}_{E/K}$
- [Absolute norm of an ideal](../../RingTheory/dedekind-domains/ideal-absolute-norm.md), for the norm $q$ of a prime ideal $\mathfrak{p}$

## Proof depends on

This node has no prerequisites.

## Sources

- M. Kirschmer, *Definite quadratic and hermitian forms with small class number*, Habilitationsschrift,
  RWTH Aachen University (2016), <http://www.math.rwth-aachen.de/~Markus.Kirschmer/papers/herm.pdf>:
  Definitions 2.1.1–2.1.3 (Hermitian spaces), 2.2.2 (lattices), 2.3.3 and 2.3.5 (dual, integral and unimodular
  lattices), item 1 of Section 2.4 (definite spaces), Definition 2.4.2 (genus); Chapter 4: the relative discriminant
  $\mathfrak{d}_{E/K} = N(\mathfrak{D})$ at the start of the chapter, Definition 4.2.1 (mass), Definition 4.2.2 (local density),
  Definition 4.2.6 (local factors) and the table of the types of $H_{\mathfrak{p}}$ after it, and the table of dimensions
  and numbers of points after Lemma 4.2.5 (p. 53).
