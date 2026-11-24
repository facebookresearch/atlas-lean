# Perfect special honest-verifier zero knowledge of the quadratic-residuosity protocol

In a finite commutative group, for $y = s^2$ and each bit $b$, the honest pair (commitment, answer)
of the [quadratic-residuosity protocol](sigma.md), with uniform prover coins $r$, has exactly the distribution of
[GMR's simulator](sim-at.md) for $b$. For $b = 1$, the pair $(r^2, r s)$ is $(w^2 y^{-1}, w)$ with
$w = r s$, uniform when $r$ is.

## Sources

- S. Goldwasser, S. Micali and C. Rackoff, "The knowledge complexity of interactive proof systems", SIAM J. Comput. 18 (1989), 186-208, Section 5, proof of Theorem 1.
