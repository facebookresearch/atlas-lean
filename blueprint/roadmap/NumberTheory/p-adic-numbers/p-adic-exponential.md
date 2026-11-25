# The p-adic exponential on a neighbourhood of zero

Let $K$ be a finite extension of $\mathbb{Q}_p$, with normalized valuation $\mathrm{ord}_K$, ring of integers
$\mathcal{O}_K$ and unit group $U_K = \mathcal{O}_K^\times$. The exponential series

$$\exp(x) = \sum_{k \ge 0} \frac{x^k}{k!}$$

converges for $\mathrm{ord}_K(x) > \mathrm{ord}_K(p) / (p - 1)$. There is an open subgroup $V$ of the
additive group $\mathcal{O}_K$ on which $\exp$ converges and defines an isomorphism of topological groups
from $V$ onto an open subgroup of $U_K$, whose inverse is given by the logarithm series

$$\log(y) = \sum_{k \ge 1} (-1)^{k+1} \frac{(y - 1)^k}{k}.$$

Since $\mathcal{O}_K$ and $U_K$ are compact, $V$ and $\exp(V)$ have finite index in $\mathcal{O}_K$ and in
$U_K$.

For $K = \mathbb{Q}_p$ the convergence comes from Legendre's formula
$\mathrm{ord}_p(k!) = (k - s_p(k)) / (p - 1)$, where $s_p(k)$ is the sum of the base-$p$ digits of $k$: the
terms $x^k / k!$ tend to $0$ exactly when $\mathrm{ord}_p(x) > 1 / (p - 1)$.

## Depends on

- [Completed field at a rational place](../algebraic-number-theory/adeles-class-field-theory/places-and-completions-of-the-rationals/completed-field.md), for $\mathbb{Q}_p$ with its $p$-adic absolute value, of which $K$ is a finite extension
- [The ring of p-adic integers](p-adic-integers.md), for $\mathbb{Z}_p$, the ring $\mathcal{O}_K$ when $K = \mathbb{Q}_p$
- [Spectral-norm unit ball is the integral closure](spectral-norm-on-algebraic-extensions/spectral-norm-le-one-iff-is-integral.md), for $\mathcal{O}_K$, the closed unit ball of $K$ for the absolute value extending that of $\mathbb{Q}_p$, which is the integral closure of $\mathbb{Z}_p$ in $K$

## Proof depends on

- [Legendre's formula with integer summands](../distribution-of-primes/prime-gaps-short-intervals/breusch-s-theorem-on-primes-between-x-and-9x-8/part-07/legendre-sum9.md), for $\mathrm{ord}_p(k!) = \sum_{j \ge 1} \lfloor k/p^j \rfloor$, which is at most $(k - 1)/(p - 1)$ for $k \ge 1$
- [Additive valuations scale by the ramification index](../../RingTheory/ramification/ramification-index-and-inertia-degree/add-val-algebra-map-eq-ramification-idx.md), for $\mathrm{ord}_K(k!) = e \cdot \mathrm{ord}_p(k!)$ with $e = \mathrm{ord}_K(p)$, applied to $\mathbb{Z}_p \to \mathcal{O}_K$: then $\mathrm{ord}_K(x^k/k!) \ge \mathrm{ord}_K(x) + (k - 1)(\mathrm{ord}_K(x) - e/(p - 1))$, which tends to infinity when $\mathrm{ord}_K(x) > e/(p - 1)$, and similarly for the terms of $\log$; so for an integer $r > e/(p - 1)$, $\exp$ maps $V = \mathfrak{m}_K^r$ into $1 + V$ and $\log$ maps $1 + V$ into $V$
- [Formal exponential turns sums into products](../../RingTheory/formal-power-series/exponential-of-multivariate-formal-power-series/exp-of-constant-coeff-zero-add.md), for $\exp(X + Y) = \exp(X)\exp(Y)$ in $\mathbb{Q}[[X, Y]]$
- [Power series identities over complete non-archimedean fields](power-series-identities-over-complete-nonarchimedean-fields.md), for evaluating at points of $V$: the formal identity above by Cauchy products, which gives $\exp(x + y) = \exp(x)\exp(y)$ for $x, y \in V$, and $\exp(\log(1 + X)) = 1 + X$ and $\log(\exp(X)) = X$ by substitution, whose conditions the estimates above give on $1 + V$ and on $V$, so that $\exp \colon V \to 1 + V$ and $\log \colon 1 + V \to V$ are mutually inverse; their domains are these balls, not the sets where the series converge
- [Compactness of the completed ring of integers](../algebraic-number-theory/adeles-class-field-theory/adeles-and-ideles/is-compact-adic-completion-integers.md), for the compactness of $\mathbb{Z}_p$, the case of $\mathbb{Q}$ and the prime $p$
- [Valuation rings dominating a complete DVR are finite over it](../../RingTheory/valuation-rings/finite-extensions-of-complete-discrete-valuation/module-finite-integer-of-is-adic-complet.md), for $\mathcal{O}_K$ being a finitely generated $\mathbb{Z}_p$-module, hence the continuous image of some $\mathbb{Z}_p^d$ and compact; $U_K$ is closed in $\mathcal{O}_K$, the complement of the open maximal ideal, hence compact, so the open subgroups $V$ and $\exp(V) = 1 + V$ have finite index

## Sources

- J. S. Milne, *Class Field Theory*, version 4.03 (2020),
  <https://www.jmilne.org/math/CourseNotes/CFT.pdf>: the proof of Lemma III.2.4 (the convergence region
  and the isomorphism of an open neighbourhood of $0$ onto an open neighbourhood of $1$ with inverse
  $\log$), used again in the proof of Proposition VII.6.8.
- J. S. Milne, *Algebraic Number Theory*, version 3.08 (2020),
  <https://www.jmilne.org/math/CourseNotes/ANT.pdf>: Example 7.29 (convergence of $\exp$ on
  $\mathbb{Q}_p$).
