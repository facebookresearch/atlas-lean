# The graph-isomorphism protocol as a Sigma protocol

One round of the zero-knowledge proof of Goldreich, Micali and Wigderson for graph isomorphism, for
simple graphs on a vertex type $V$. A statement is a pair $(G_0, G_1)$; a witness is a permutation
$\varphi$ of $V$ that maps $G_0$ onto $G_1$. The prover's coins are a permutation $\pi$ of $V$ (drawn
uniformly when $V$ is finite), and it commits to $H = \pi(G_1)$. On the challenge $\alpha$ it answers $\pi$ if $\alpha = 1$ and $\pi \circ \varphi$ if
$\alpha = 0$. The verifier accepts an answer $\sigma$ when $\sigma$ maps
[the graph selected by $\alpha$](pick-graph.md) onto $H$.

## Sources

- O. Goldreich, S. Micali and A. Wigderson, "Proofs that yield nothing but their validity or all languages in NP have zero-knowledge proof systems", J. ACM 38 (1991), 691-729, Section 2.2, Protocol 2 (one of the $m$ iterations; the case of a challenge outside
  $\{0, 1\}$ does not arise here, the challenge set being exactly the two bits).
