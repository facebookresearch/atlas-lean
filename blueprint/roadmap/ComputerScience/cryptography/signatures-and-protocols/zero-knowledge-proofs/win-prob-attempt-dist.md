# One rewinding attempt simulates the real view

Let a Sigma protocol have a perfect special honest-verifier zero-knowledge simulator and a finite
challenge set $\mathrm{Ch}$, and let $x$ have a witness $w$. For every verifier $V^*$ and every test $T$
of its view,

$$\Pr[\text{the attempt succeeds and } T \text{ holds}] = \frac{1}{\lvert \mathrm{Ch} \rvert} \Pr[T \text{ holds of the real view}],$$

the left side for [one rewinding attempt](attempt-dist.md) and the right side for
[the real view](real-view-dist.md). Taking $T$ always true, an attempt succeeds with probability exactly
$1/\lvert \mathrm{Ch} \rvert$ whatever $V^*$ does; conditioned on success, the simulated view has exactly
the distribution of the real view.

Here each attempt redraws the verifier's coins ([one rewinding attempt](attempt-dist.md)); the cited
proofs fix them and retry only the guess.

The proof: by [special honest-verifier zero knowledge](special-hvzk.md) the simulator's pair for the
guess $e'$ is distributed as the honest pair for the challenge $e'$, and the successful triples
$(r, e', k)$ with $e' = V^*(a_k, r)$ are in bijection with the real runs $(r, k)$.

## Sources

- S. Goldwasser, S. Micali and C. Rackoff, "The knowledge complexity of interactive proof systems", SIAM J. Comput. 18 (1989), 186-208, Section 5, proof of Theorem 1.
- O. Goldreich, S. Micali and A. Wigderson, "Proofs that yield nothing but their validity or all languages in NP have zero-knowledge proof systems", J. ACM 38 (1991), 691-729, proof of Theorem 2 ("from the point of view of $V^*$, the case which leads to [the
  simulator's] success and the case which leads to a failure look identical").
