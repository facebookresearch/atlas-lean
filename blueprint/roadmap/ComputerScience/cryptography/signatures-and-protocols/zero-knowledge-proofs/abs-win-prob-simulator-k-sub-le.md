# Zero knowledge against an arbitrary verifier, one round

Let a Sigma protocol have a perfect special honest-verifier zero-knowledge simulator and a finite
challenge set $\mathrm{Ch}$, and let $x$ have a witness. For every verifier $V^*$ (its challenge any
function of the commitment and of its coins), every test $T$ of its view and every $k$, the
[rewinding simulator with $k$ attempts](simulator-k.md), which never sees the witness, and
[the real interaction](real-view-dist.md) produce views passing $T$ with probabilities that differ by
at most $(1 - 1/\lvert \mathrm{Ch} \rvert)^k$, a failed simulation counting as failing $T$. (For
tests that count a failed simulation as passing, the gap is
$(1 - 1/\lvert \mathrm{Ch} \rvert)^k (1 - \Pr[T])$, so the statistical distance between the two
views is also at most $(1 - 1/\lvert \mathrm{Ch} \rvert)^k$.)

For a two-element challenge set the error is $2^{-k}$. Goldwasser, Micali and Rackoff's Theorem 1 (for
quadratic residuosity) and Goldreich, Micali and Wigderson's Theorem 2 (for graph isomorphism) assert
perfect zero knowledge for the whole $m$-round protocol with an expected polynomial-time simulator;
here one round is simulated and the simulator is truncated.

## Informally uses

- [The truncated rewinding simulator reproduces the real view](win-prob-simulator-k.md)

## Sources

- S. Goldwasser, S. Micali and C. Rackoff, "The knowledge complexity of interactive proof systems", SIAM J. Comput. 18 (1989), 186-208, Section 5, Theorem 1 and its proof.
- O. Goldreich, S. Micali and A. Wigderson, "Proofs that yield nothing but their validity or all languages in NP have zero-knowledge proof systems", J. ACM 38 (1991), 691-729, Theorem 2 and Definition 5 (zero knowledge via the distribution of the verifier's read-only
  tapes: input, coins and received messages).
