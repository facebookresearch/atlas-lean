# Multiplication by n as a Galois covering

Let $A$ be an [abelian variety](../abelian-scheme.md) of dimension $g$ over a separably closed field
$k$, with zero $0$, and let $n \ge 1$ be an integer not divisible by the characteristic of $k$.
Write $A_n(k)$ for the group of points of $A(k)$ killed by $n$.

1. Multiplication by $n$, $n_A \colon A \to A$, is a finite étale covering, and the group $A_n(k)$,
   acting on $A$ by translations, makes it a Galois covering with group $A_n(k)$: the morphism
   $A \times A_n(k) \to A \times_{n_A, A, n_A} A$, $(a, x) \mapsto (a, a + x)$, is an isomorphism.
2. Let $\pi_1(A, 0)$ be the
   [étale fundamental group](../../grothendieck-topologies/etale-fundamental-group-and-first-cohomology.md)
   at a geometric point over $0$. The fibre of $n_A$ over $0$ is $A_n(k)$, and
   $\rho_n(\gamma) = \gamma \cdot 0$ defines a continuous homomorphism
   $\rho_n \colon \pi_1(A, 0) \to A_n(k)$, which is surjective. For $m \mid n$,
   $\rho_m = (n/m) \rho_n$.
3. For a prime $\ell$ different from the characteristic of $k$, the $\rho_{\ell^m}$ define a
   continuous surjection $\pi_1(A, 0) \to T_\ell A = \varprojlim_m A_{\ell^m}(k)$, the transition maps
   being multiplication by $\ell$.
4. The map $\operatorname{Hom}(A_n(k), \mathbb{Z}/n\mathbb{Z}) \to H^1(A_{\mathrm{et}}, \mathbb{Z}/n\mathbb{Z})$,
   $f \mapsto f \circ \rho_n$, through the identification of $H^1(A_{\mathrm{et}}, \mathbb{Z}/n\mathbb{Z})$
   with $\operatorname{Hom}_{\mathrm{cont}}(\pi_1(A, 0), \mathbb{Z}/n\mathbb{Z})$, is injective.

For 1, $n_A$ is finite, étale and surjective with kernel $A[n]$, the constant group scheme on
$A_n(k)$, and $A$ is commutative, so translations by $A_n(k)$ commute with $n_A$; the morphism in 1 is
the isomorphism $A \times A[n] \cong A \times_A A$ for the kernel of a homomorphism. For 2, $\pi_1(A, 0)$
acts on the fibre $A_n(k)$ commuting with the translations, so
$\gamma \cdot x = x + \rho_n(\gamma)$, which makes $\rho_n$ a homomorphism; it is surjective because the
covering $A$ is connected, so that the action on the fibre is transitive. The morphism
$(n/m)_A$ is a morphism of coverings from $n_A$ to $m_A$ that sends $0$ to $0$, which gives
$\rho_m = (n/m) \rho_n$. For 3, a compatible family of surjections from the compact group
$\pi_1(A, 0)$ onto finite groups gives a surjection onto their limit. For 4, $f \circ \rho_n = 0$
forces $f = 0$ as $\rho_n$ is surjective.

## Depends on

- [Abelian scheme](../abelian-scheme.md), for abelian varieties over a field
- [The étale fundamental group and first étale cohomology with finite coefficients](../../grothendieck-topologies/etale-fundamental-group-and-first-cohomology.md),
  for $\pi_1(A, 0)$ and $H^1(A_{\mathrm{et}}, \mathbb{Z}/n\mathbb{Z})$

## Proof depends on

- [Isogenies of abelian schemes](../isogenies-of-abelian-schemes.md), for $n_A$ finite, étale and
  surjective, with kernel the constant group scheme on the $n^{2g}$ points of $A_n(k)$ (its items 2
  and 3)
- [Homomorphisms of abelian schemes and commutativity](../homomorphisms-of-abelian-schemes.md), for the
  commutativity of $A$
- [The étale fundamental group and first étale cohomology with finite coefficients](../../grothendieck-topologies/etale-fundamental-group-and-first-cohomology.md),
  for the classification of finite étale coverings, the transitivity of the action on the fibre of a
  connected covering (its item 1), and the identification of $H^1$ (its item 2)

## Sources

- J. S. Milne, *Abelian Varieties*, course notes, version 2.00 (2008), <https://www.jmilne.org/math/CourseNotes/AV.pdf>: Chapter I, Theorem 7.2, p. 33, and Remark 7.3, p. 34; §12, the paragraph after Theorem
  12.1, p. 55 (multiplication by $\ell^n$ is a finite étale covering with group of covering
  transformations $A_{\ell^n}(k)$, the epimorphism $\pi_1(A, 0) \to A_{\ell^n}(k)$, with a reference
  to Milne's *Étale Cohomology*, I 5, its limit $\pi_1(A, 0) \to T_\ell A$, and the injection
  $\operatorname{Hom}_{\mathbb{Z}_\ell}(T_\ell A, \mathbb{Z}_\ell) \to H^1(A, \mathbb{Z}_\ell)$); Remark
  12.3, p. 56.
- J. S. Milne, *Étale Cohomology*, Princeton University Press, 1980: I 5, as cited by Milne,
  *Abelian Varieties*, p. 55 (not read).
