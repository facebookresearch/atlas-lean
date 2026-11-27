# The Pigou bound bounds the price of anarchy of nonatomic routing

Let $\mathcal C$ be a class of latency functions. For every nonatomic congestion game whose latencies lie in $\mathcal{C}$, every Wardrop equilibrium $f$ and every feasible flow $f^*$ satisfy $C(f) \le \alpha(\mathcal C)\, C(f^*)$. For the class of polynomials of degree at most $d$ with nonnegative coefficients,

$$
\alpha = \Bigl(1 - d\,(d+1)^{-(d+1)/d}\Bigr)^{-1},
$$

which is $4/3$ for $d = 1$ and grows as $\Theta(d / \ln d)$.

## Proof sketch

The variational inequality of Wardrop equilibria gives $\sum_e f_e \ell_e(f_e) \le \sum_e f^*_e \ell_e(f_e)$; applying the definition of $\alpha$ edge by edge with $r = f_e$, $x = f^*_e$ yields $f^*_e \ell_e(f_e) \le f^*_e \ell_e(f^*_e) + (1 - 1/\alpha) f_e \ell_e(f_e)$, and rearranging gives the bound. For polynomials, the supremum is computed by calculus on monomials.

## Depends on

- [Pigou bound of a class of latency functions](pigou-bound-of-a-class-of-latency-functions.md)
- [Wardrop equilibrium](../is-wardrop.md)

## Proof depends on

- [Wardrop equilibria are the minimizers of the Beckmann potential](../wardrop-equilibria-minimize-the-beckmann-potential.md)

## Sources

- Tim Roughgarden, "The Price of Anarchy is Independent of the Network Topology", Journal of Computer and System Sciences, 2003.
- Jose R. Correa, Andreas S. Schulz and Nicolas E. Stier-Moses, "Selfish Routing in Capacitated Networks", Mathematics of Operations Research, 2004.
- Tim Roughgarden, "CS364A: Algorithmic Game Theory, Lecture Notes", Stanford University, Fall 2013, 2013.
