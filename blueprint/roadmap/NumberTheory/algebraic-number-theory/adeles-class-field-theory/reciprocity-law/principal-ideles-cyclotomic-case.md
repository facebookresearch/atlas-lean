# The global Artin map of a cyclotomic extension is trivial on principal idèles

Let $K$ be a number field and let $L/K$ be a finite extension contained in $K(\zeta)$ for some root of unity
$\zeta$ (such an extension is abelian). Then the [global Artin map](global-artin-map.md)
$\phi_{L/K} \colon \mathbb{I}_K \to \mathrm{Gal}(L/K)$ is trivial on the principal idèles: $\phi_{L/K}(a) = 1$
for every $a \in K^\times$.

Milne first treats $K = \mathbb{Q}$ and $L = \mathbb{Q}(\zeta_m)$, identifying
$\mathrm{Gal}(\mathbb{Q}(\zeta_m)/\mathbb{Q})$ with $(\mathbb{Z}/m\mathbb{Z})^\times$; by restriction it
suffices to take $m = \ell^r$ for a prime $\ell$. The local Artin map at the infinite place sends a negative
number to complex conjugation, by the definition of the global Artin map; at a prime $p \ne \ell$, which is unramified, it sends $u p^s$ to
$[p]^s$ ([the global Artin map at unramified places](artin-map-at-unramified-places.md)); and at $\ell$ it
sends $u \ell^s$ to $[u]^{-1}$, by the explicit local reciprocity law for $\mathbb{Q}_\ell(\zeta_{\ell^r})$.
Multiplying the local components of $a = -1$, $a = \ell$ and $a = q$ for a prime $q \ne \ell$ gives $1$ in
each case. For general $K$, $K(\zeta_m)$ is the composite of $K$ and $\mathbb{Q}(\zeta_m)$,
$\mathrm{Gal}(K(\zeta_m)/K)$ embeds in $\mathrm{Gal}(\mathbb{Q}(\zeta_m)/\mathbb{Q})$ by restriction, and
$\phi_{K(\zeta_m)/K}(a)|_{\mathbb{Q}(\zeta_m)} = \phi_{\mathbb{Q}(\zeta_m)/\mathbb{Q}}(\mathrm{Nm}_{K/\mathbb{Q}}(a))$
by the [norm compatibility](norm-compatibility.md), with $\mathrm{Nm}_{K/\mathbb{Q}}(K^\times) \subseteq \mathbb{Q}^\times$;
a subextension $L$ of $K(\zeta_m)$ follows by restriction (Lemma VII.8.4).

## Depends on

- [Global Artin map](global-artin-map.md)

## Proof depends on

- [Norm compatibility of the global Artin map](norm-compatibility.md), for the passage from $\mathbb{Q}$ to $K$
- [The global Artin map at unramified places](artin-map-at-unramified-places.md), for the primes not dividing $m$
- [Local class field theory: functoriality and explicit reciprocity](../../../p-adic-numbers/local-class-field-theory-functoriality.md), for the local Artin map of $\mathbb{Q}_\ell$ on $\mathbb{Q}_\ell(\zeta_{\ell^r})$ (its item 2)

## Sources

- J. S. Milne, *Class Field Theory*, version 4.03 (2020),
  <https://www.jmilne.org/math/CourseNotes/CFT.pdf>: Example VII.8.2 (the case of
  $\mathbb{Q}(\zeta_m)/\mathbb{Q}$) with footnote 5 and Remark VII.8.3, Lemma VII.8.4 and the sentence after
  it ("(8.1a) holds for all cyclotomic extensions of a number field $K$"); Example I.3.13 (the local Artin
  map of $\mathbb{Q}_p$ on $\mathbb{Q}_p(\zeta_n)$).
