# The quadratic-residuosity protocol as a Sigma protocol

In a commutative group $G$: a statement is an element $y$ and a witness is an $s$ with $s^2 = y$. The
prover's coins are an element $r$ of $G$ (drawn uniformly when $G$ is finite) and it commits to
$u = r^2$; on the bit $0$ it answers $r$ and on the bit $1$ it answers
$r s$; the verifier accepts an answer $w$ when $w^2 = u$ (bit $0$) or $w^2 = u y$ (bit $1$).

## Sources

- S. Goldwasser, S. Micali and C. Rackoff, "The knowledge complexity of interactive proof systems", SIAM J. Comput. 18 (1989), 186-208, Section 5 (one of the $m$ rounds; the prover sends "a random square root" of $u$ or of
  $u y$, which $r$ and $r s$ are when $r$ is uniform).
