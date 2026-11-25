# D-infinity is a model of the beta-eta calculus

Untyped lambda terms are variables, applications $M\,N$ and abstractions $\lambda x.\, M$, identified up to renaming of bound variables. The
$\beta\eta$-calculus is the least congruence on terms containing $(\lambda x.\, M)\, N = M[N/x]$ ($\beta$) and $\lambda x.\, M\,x = M$ when $x$ is not free in $M$
($\eta$).

Let $F : D_\infty \to [D_\infty \to D_\infty]$ and $G : [D_\infty \to D_\infty] \to D_\infty$ be the mutually inverse continuous maps of
[Scott's D-infinity](scott-s-d-infinity-is-isomorphic-to-its.md). For an environment $\rho$ assigning elements of $D_\infty$ to variables, define

$$[\![x]\!]\rho = \rho(x), \qquad [\![M\,N]\!]\rho = F([\![M]\!]\rho)([\![N]\!]\rho), \qquad [\![\lambda x.\, M]\!]\rho = G\big(d \mapsto [\![M]\!]\rho[x \mapsto d]\big).$$

Then for all terms:

1. $[\![M]\!]\rho$ is Scott-continuous in each value $\rho(x)$, so the map $d \mapsto [\![M]\!]\rho[x \mapsto d]$ in the last clause lies in $[D_\infty \to D_\infty]$;
2. substitution: $[\![M[N/x]]\!]\rho = [\![M]\!]\rho[x \mapsto [\![N]\!]\rho]$;
3. soundness: if $M = N$ in the $\beta\eta$-calculus, then $[\![M]\!]\rho = [\![N]\!]\rho$ for every $\rho$.

$\beta$ holds because $F \circ G = \mathrm{id}$, and $\eta$ because $G \circ F = \mathrm{id}$. In Scott's graph model only $\beta$ holds, since there the function space is only a
retract.

## Depends on

- [Scott's D-infinity is isomorphic to its function space](scott-s-d-infinity-is-isomorphic-to-its.md)

## Proof depends on

- [Scott's D-infinity is isomorphic to its function space](scott-s-d-infinity-is-isomorphic-to-its.md)
- [Scott-continuous maps and least fixed points](../../../Order/fixed-points-domain-theory/scott-continuous-maps-and-least-fixed-points/README.md)

## Sources

- D. Scott, *Continuous Lattices*, Technical Monograph PRG-7, Oxford University Computing Laboratory, 1971, <http://www.cs.ox.ac.uk/files/3229/PRG07.pdf>: Theorem 4.4 (the isomorphism used for application and abstraction).
- S. Abramsky and A. Jung, "Domain theory", in *Handbook of Logic in Computer Science*, Vol. 3, Oxford University Press, 1994, <https://www.cs.bham.ac.uk/~axj/pub/papers/handy1.pdf>: Section 5.1.1 (a solution of $X \cong [X \to X]$, with the isomorphisms explicit, gives a model of the untyped λ-calculus). The three numbered properties are derived on this page.
- H. P. Barendregt, *The Lambda Calculus: Its Syntax and Semantics*, revised ed., North-Holland, 1984.
