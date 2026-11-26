# Integer perturbation of best response polytopes recovers exact rational equilibria

There is a polynomial $E(m, n, \log H)$ such that the following holds. Let $A, B$ be $m \times n$ integer matrices with entries in $[1, H]$, and let $K = 2^{E(m, n, \log H)}$. The perturbed polytopes $P_\varepsilon = \{x \ge 0 : B^\top x \le K^n \mathbf 1 + (K^{n-1-j})_j\}$ and $Q_\varepsilon = \{y \ge 0 : A y \le K^m \mathbf 1 + (K^{m-1-i})_i\}$ are nondegenerate, and from every nonzero completely labelled vertex pair of $(P_\varepsilon, Q_\varepsilon)$ an exact rational Nash equilibrium of $(A, B)$ is computable by Cramer's rule, with numerators and denominators of bit length polynomial in $m$, $n$ and $\log H$.

## Proof sketch

Powers of a sufficiently large base $K$ act as a symbolic lexicographic perturbation: Hadamard's bound shows every basis determinant is smaller than $K$, so no vertex can satisfy an extra constraint, and the basis structure of a perturbed vertex determines an unperturbed completely labelled pair.

## Depends on

- [Best response polytopes of a bimatrix game](best-response-polytopes-of-a-bimatrix-game.md)
- [Completely labelled vertex pairs are exactly the Nash equilibria](completely-labelled-vertex-pairs-are-exactly-the-nash-equilibria.md)

## Sources

- Bernhard von Stengel, "Equilibrium Computation for Two-Player Games in Strategic and Extensive Form", Algorithmic Game Theory, Cambridge University Press, 2007.
- Christos H. Papadimitriou, "On the Complexity of the Parity Argument and Other Inefficient Proofs of Existence", Journal of Computer and System Sciences, 1994.
