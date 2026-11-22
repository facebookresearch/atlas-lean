# Solver for the key equations

For a field $F$, points $\alpha_0, \dots, \alpha_{n-1} \in F$
and parameters $k, e \in \mathbb{N}$, a solver for the Berlekamp-Welch key equations is a
procedure that takes a received word $y \in F^n$ and either returns a pair of polynomials
$(Q, E)$ over $F$ or reports failure, such that every returned pair solves the key equations for
$y$, and a pair is returned whenever the key equations for $y$ have a solution.

(The key equations are a linear system in the coefficients of $Q$ and of $E$; Gaussian
elimination is a solver.)
