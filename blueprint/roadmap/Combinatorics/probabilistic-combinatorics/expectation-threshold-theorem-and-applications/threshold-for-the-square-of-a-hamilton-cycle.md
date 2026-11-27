# Kahn-Narayanan-Park: the threshold for the square of a Hamilton cycle

The threshold for $G(n, p)$ to contain the square of a Hamilton cycle (the graph on a cyclic ordering joining vertices at cyclic distance $1$ or $2$) is $p = \Theta(1/\sqrt n)$, resolving a conjecture of Kühn and Osthus.

## Proof sketch

The lower bound is a first moment count. For the upper bound, show that the uniform measure on squares of Hamilton cycles in $K_n$ is $O(\sqrt n)^{-1}$-spread in a weak sense adapted to the number of components of a fixed edge set, and run the FKNP iterative fragment argument, which here loses no logarithmic factor because the obstructions to spreadness are controlled component by component.

## Depends on

- [The threshold $p_c(\mathcal F)$](../thresholds-and-expectation-thresholds/p-c.md)

## Proof depends on

- [Thresholds versus fractional expectation-thresholds](../thresholds-and-expectation-thresholds/theorem-1-1.md)
- [Spread families and spread measures](../../extremal-set-theory/spread-families-and-robust-sunflowers/kappa-spread-families-and-measures.md)
- [Park-Pham theorem: thresholds are within a logarithmic factor of expectation thresholds](park-pham-theorem.md)

## Sources

- Jeff Kahn, Bhargav Narayanan, Jinyoung Park, "The threshold for the square of a Hamilton cycle", Proceedings of the AMS 149(8) (2021); arXiv:2010.08592.
