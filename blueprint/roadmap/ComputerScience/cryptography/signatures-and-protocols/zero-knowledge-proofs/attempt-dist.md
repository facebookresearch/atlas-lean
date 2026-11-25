# One rewinding attempt

For a per-challenge simulator, a statement $x$ and a verifier $V^*$: draw the verifier's coins $r$ and
a guess $e'$ of its challenge, let the simulator produce a commitment and an answer $(a, z)$ for $e'$
from the statement alone, and output whether $V^*(a, r) = e'$, together with the simulated view
$(r, a, z)$. Each attempt draws fresh verifier coins together with the fresh guess, whereas
Goldwasser, Micali and Rackoff's machine $M$ and Goldreich, Micali and Wigderson's simulator fix the
verifier's random tape once and retry only the guess. For one round with a perfect special
honest-verifier simulator both work; fixing the tape is what composing rounds needs.

## Sources

- S. Goldwasser, S. Micali and C. Rackoff, "The knowledge complexity of interactive proof systems", SIAM J. Comput. 18 (1989), 186-208, Section 5, proof of Theorem 1 (the simulator $M$ picks a random bit and a random $w$, and
  outputs the round only if the verifier's bit agrees).
- O. Goldreich, S. Micali and A. Wigderson, "Proofs that yield nothing but their validity or all languages in NP have zero-knowledge proof systems", J. ACM 38 (1991), 691-729, proof of Theorem 2.
