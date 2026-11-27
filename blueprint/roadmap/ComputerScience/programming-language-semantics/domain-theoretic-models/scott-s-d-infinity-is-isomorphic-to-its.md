# Scott's D-infinity is isomorphic to its function space

Let $D_0$ be a continuous lattice and let $i_0 : D_0 \to D_1$, $j_0 : D_1 \to D_0$ be a projection pair onto $D_1 = [D_0 \to D_0]$, the lattice of
Scott-continuous self-maps ordered pointwise: $j_0 \circ i_0 = \mathrm{id}$ and $i_0 \circ j_0 \le \mathrm{id}$. Define $D_{n+1} = [D_n \to D_n]$ and lift the pair
level by level,

$$i_{n+1}(f) = i_n \circ f \circ j_n, \qquad j_{n+1}(g) = j_n \circ g \circ i_n,$$

so that each $(i_n, j_n)$ makes $D_n$ a projection of $D_{n+1}$. Let $D_\infty$ be the inverse limit of the system $(D_n, j_n)$: the sequences $(x_n)$ with
$x_n \in D_n$ and $j_n(x_{n+1}) = x_n$ for all $n$. Then:

- $D_\infty$ is a continuous lattice, and each $D_n$ is a projection of $D_\infty$;
- $D_\infty$ is homeomorphic, and so order-isomorphic, to $[D_\infty \to D_\infty]$, by the mutually inverse continuous maps

$$F(x) = \bigsqcup_n i_{n\infty} \circ x_{n+1} \circ j_{\infty n}, \qquad G(f) = \bigsqcup_n i_{(n+1)\infty}(j_{\infty n} \circ f \circ i_{n\infty}),$$

where $j_{\infty n} : D_\infty \to D_n$ is the $n$-th projection and $i_{n\infty} : D_n \to D_\infty$ the corresponding embedding.

The function-space isomorphism uses this particular lifted system of projections; it is not claimed for arbitrary embedding–projection
pairs between the same lattices.

## Depends on

- [Scott's inverse-limit theorem](../../../Order/fixed-points-domain-theory/scott-s-inverse-limit-theorem.md)

## Sources

- D. Scott, *Continuous Lattices*, Technical Monograph PRG-7, Oxford University Computing Laboratory, 1971, <http://www.cs.ox.ac.uk/files/3229/PRG07.pdf>: Proposition 3.7 (lifting a projection pair to function spaces), Section 4 (inverse systems and limits), Propositions 4.1–4.2 and Theorem 4.4 with the formulas for the homeomorphism in its proof. This monograph is the version of the paper in *Toposes, Algebraic Geometry and Logic*, LNM 274, Springer, 1972.
- H. P. Barendregt, *The Lambda Calculus: Its Syntax and Semantics*, revised ed., North-Holland, 1984.
