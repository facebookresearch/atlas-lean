# Von Neumann mean ergodic theorem

A measure-preserving map $T$ acts on square-integrable functions by its Koopman operator $U_T f = f \circ T$, a
linear isometry of $L^2(\mu)$. Von Neumann's mean ergodic theorem, the first ergodic theorem (1932), says that the
ergodic averages $\frac1N \sum_{k<N} f \circ T^k$ converge in $L^2(\mu)$ to the orthogonal projection of $f$ onto
the invariant functions. It is the Hilbert-space counterpart of the almost-everywhere convergence in the
[Birkhoff ergodic theorem](../birkhoff-ergodic-theorem/README.md); for a stationary sequence it is a weak law of
large numbers in mean square.

- [Koopman operator](koopman.md)
- [The Koopman operator is composition with $T$](koopman-apply-ae-eq.md)
- [The Koopman operator is a contraction](norm-koopman-le.md)
- [Von Neumann's mean ergodic theorem](tendsto-birkhoff-average-koopman.md)

## Related topics

- [Birkhoff ergodic theorem](../birkhoff-ergodic-theorem/README.md): almost-everywhere convergence of the same
  averages for integrable functions.
