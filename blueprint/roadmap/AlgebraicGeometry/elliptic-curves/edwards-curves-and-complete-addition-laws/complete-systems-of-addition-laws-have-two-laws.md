# A complete system of addition laws needs exactly two laws

On an elliptic curve in Weierstrass form, the smallest complete system of addition laws has two laws, and two laws forming a complete system both have bidegree $(2,2)$ (Bosma–Lenstra).

**Theorem.** Let $E$ be an elliptic curve over a field $k$ given by a Weierstrass equation. The smallest cardinality of a complete system of addition laws on $E$ is two, and if two addition laws form a complete system then each of them has bidegree $(2,2)$.

In particular no single addition law is free of exceptional pairs over all extensions of $k$. A single formula that is complete for the $k$-rational points of some other model, such as a twisted Edwards curve with $a$ square and $d$ non-square, is a different notion and does not contradict this.

## Depends on

- [Addition laws and complete systems on a Weierstrass curve](addition-laws-on-a-weierstrass-curve.md)

## Proof depends on

- [Exceptional pairs of addition laws of bidegree (2,2)](exceptional-pairs-of-bidegree-two-two-addition-laws.md)

## Expansion

Section 3: for a nonzero law of bidegree $(\mu,\nu)$ with $h=Z_3Z_1^{-\mu}Z_2^{-\nu}$, the *exceptional divisor* $D=(h)+3\mu V+3\nu H-3\nabla$ is effective, linearly equivalent to $3\mu V+3\nu H-3\nabla$, and its support is the set of exceptional pairs. Intersecting with the graph $\Gamma_n$ of multiplication by $n$, using $V\cdot\Gamma_n=1$, $H\cdot\Gamma_n=n^2$, $\nabla\cdot\Gamma_n=(n+1)^2$, gives $3(\mu+n^2\nu-(n+1)^2)\ge0$ for almost all $n$, so $\nu\ge2$, and by symmetry $\mu\ge2$. A single complete law would have $D=0$, contradicting its bidegree $(3\mu-3,3\nu-3)\ne(0,0)$. For two laws of bidegrees $(\mu,\nu)$ and $(\kappa,\lambda)$ forming a complete system, the exceptional divisors are disjoint, so their intersection number is $0$; with $V\cdot H=V\cdot\nabla=H\cdot\nabla=1$ and $V\cdot V=H\cdot H=\nabla\cdot\nabla=0$ this gives $(\mu-1)(\lambda-1)+(\nu-1)(\kappa-1)=2$, forcing $\mu=\nu=\kappa=\lambda=2$. Existence of a complete system of two laws follows from the exceptional-pair theorem. Prerequisites still to add: divisors on the surface $E\times E$, the pullbacks $V$, $H$, $\nabla$ of $O$ under the two projections and the addition map, and their intersection numbers. The degree of the multiplication map and the graphs $\Gamma_n$ are needed as well.

## Sources

- W. Bosma and H. W. Lenstra, Jr., "Complete systems of two addition laws for elliptic curves", *Journal of Number Theory* 53(2):229–240, 1995, doi:10.1006/jnth.1995.1088, Theorem 1, Section 3 (pp. 233–234) and the discussion after Theorem 2.
