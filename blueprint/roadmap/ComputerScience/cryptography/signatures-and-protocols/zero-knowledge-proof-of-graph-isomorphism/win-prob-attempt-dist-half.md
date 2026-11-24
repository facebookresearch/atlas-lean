# One rewinding attempt for the graph-isomorphism protocol

For isomorphic graphs on a finite vertex type with witness $\varphi$, every verifier $V^*$ (its challenge any function of the
prover's graph $H$ and of its coins) and every test $T$ of its view, one attempt of the simulator
(guess $\alpha'$, send $\sigma(G_{\alpha'})$ for a uniform $\sigma$, keep the attempt if $V^*$ asks
$\alpha'$) succeeds and passes $T$ with probability exactly half the probability that the real view
passes $T$.

## Informally uses

- [One rewinding attempt simulates the real view](../zero-knowledge-proofs/win-prob-attempt-dist.md)
- [Perfect special honest-verifier zero knowledge of the graph-isomorphism protocol](sigma-special-hvzk.md)

## Sources

- O. Goldreich, S. Micali and A. Wigderson, "Proofs that yield nothing but their validity or all languages in NP have zero-knowledge proof systems", J. ACM 38 (1991), 691-729, proof of Theorem 2.
