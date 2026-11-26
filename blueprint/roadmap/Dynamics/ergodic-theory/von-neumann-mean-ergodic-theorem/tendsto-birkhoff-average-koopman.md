# Von Neumann's mean ergodic theorem

Let $T$ be a measurable map preserving a measure $\mu$, let $U_T f = f \circ T$ be its
[Koopman operator](koopman.md) on the real space $L^2(\mu)$, and let $P$ be the orthogonal projection of $L^2(\mu)$ onto the closed subspace
$\{f : U_T f = f\}$ of invariant functions. For every $f \in L^2(\mu)$,

$$\frac{1}{N} \sum_{k=0}^{N-1} f \circ T^k \longrightarrow P f \qquad \text{in } L^2(\mu).$$

The standard proof is Hilbert-space geometry: $L^2(\mu)$ splits orthogonally into the invariant functions, on which the
averages are constant, and the closure of the coboundaries $g \circ T - g$, on which they telescope to $0$;
the isometry $U_T$ is a contraction, which is all the argument needs, so the same convergence holds for every
contraction of a Hilbert space. The source also states that the limit is the constant $\int f \, d\mu$ when
$\mu$ is a probability measure and $T$ is ergodic; that second statement is not part of the statement above.

## Sources

- O. Sarig, *Lecture Notes on Ergodic Theory* (2023), §2.1, Theorem 2.1 (von Neumann's Mean Ergodic Theorem); the
  limit for nonergodic maps is identified as the projection onto the invariant functions at the start of §2.3
  (The non-ergodic case).
