# The global Artin map at unramified places

Let $L/K$ be a finite abelian extension of number fields with
[global Artin map](global-artin-map.md) $\phi_{L/K} \colon \mathbb{I}_K \to \mathrm{Gal}(L/K)$, and let $v$
be a finite place of $K$, with prime ideal $\mathfrak{p}_v$, that is unramified in $L$. For $x \in K_v^\times$
let $\iota_v(x) \in \mathbb{I}_K$ be the idèle with component $x$ at $v$ and $1$ at the other places. Then:

1. for every uniformizer $\pi_v$ of $K_v$, $\phi_{L/K}(\iota_v(\pi_v)) = (\mathfrak{p}_v, L/K)$, the
   Frobenius element of $\mathfrak{p}_v$: the unique $\sigma \in \mathrm{Gal}(L/K)$ with
   $\sigma(x) \equiv x^{N\mathfrak{p}_v} \pmod{\mathfrak{P}}$ for all $x \in \mathcal{O}_L$, for a prime
   $\mathfrak{P}$ of $\mathcal{O}_L$ above $\mathfrak{p}_v$, which does not depend on $\mathfrak{P}$ since
   $L/K$ is abelian;
2. $\phi_{L/K}(\iota_v(u)) = 1$ for every unit $u \in \mathcal{O}_v^\times$.

Consequently, if $\mathfrak{m}$ is a modulus of $K$ such that every prime not dividing its finite part
$\mathfrak{m}_0$ is unramified in $L$, and $a \in \mathbb{I}_K$ has component $1$ at the infinite places
and at the primes dividing $\mathfrak{m}_0$, then $\phi_{L/K}(a)$ is the image under the
[Artin map](../artin-map/artin-map.md) of the fractional ideal
$\prod_{v} \mathfrak{p}_v^{\mathrm{ord}_v(a_v)}$, which is coprime to $\mathfrak{m}_0$.

Under the identification of $\mathrm{Gal}(L_w/K_v)$ with the decomposition group of a place $w \mid v$,
the Frobenius element of the unramified extension $L_w/K_v$ is $(\mathfrak{p}_v, L/K)$; so part 1 is the
normalization of the [local Artin map](../../../p-adic-numbers/local-class-field-theory.md), and part 2
is its triviality on units over unramified extensions. The consequence follows by multiplicativity, the
Artin map sending each prime $\mathfrak{p}_v$ to its Frobenius element.

## Depends on

- [Global Artin map](global-artin-map.md)
- [In an abelian group the Frobenius element depends only on the prime below](../../../../RingTheory/ramification/frobenius-elements/arith-frob-at-eq-of-under-eq.md)
- [Artin map](../artin-map/artin-map.md), for the consequence

## Proof depends on

- [Local class field theory: the local Artin map](../../../p-adic-numbers/local-class-field-theory.md), for the action of a uniformizer and of the units on an unramified extension
- [The Artin map at a prime](../artin-map/artin-map-prime-coprime-unit.md), for the consequence

## Sources

- J. S. Milne, *Class Field Theory*, version 4.03 (2020),
  <https://www.jmilne.org/math/CourseNotes/CFT.pdf>: Summary V.5.10(b) (part 1), the proof of
  Proposition V.5.2 (part 2), Remark V.5.8 (the global Artin map restricted to idèles with trivial
  components at a finite set of places is the Artin map on ideals), and the paragraph after Theorem
  VII.8.1 ("$\phi_{L/K}$ maps the idèle with a prime element in $v$-position to the Frobenius element
  $(\mathfrak{p}_v, L/K)$").
- A. V. Sutherland, *Number Theory I* (MIT 18.785, Fall 2021), Lecture 28,
  <https://math.mit.edu/classes/18.785/2021fa/LectureNotes28.pdf>: Section 28.2
  ($\phi_w(\theta_{L_w/K_v}(\pi_v)) = \mathrm{Frob}_v$ at an unramified place).
