# Direct secret recovery from a trained LWE model

Direct recovery queries a model trained to predict $b=a\cdot s+e$ on the inputs $a=Ke_i$: a model that has learned the binary secret returns about $0$ when $s_i=0$ and about $K$ when $s_i=1$. Scores over several values of $K$ give a candidate secret.

Let $s\in\{0,1\}^n$ be the secret and $M$ a model trained on samples $(a,b)$, $b=a\cdot s+e \bmod q$, whose outputs are read as integers in $[0,q)$. For $K\in\mathbb{Z}_q$ and the $i$-th standard basis vector $e_i$, the exact label of $Ke_i$ would be $Ks_i+e$.

**Rule (SALSA PICANTE).** Choose values $K_1,\dots,K_J\in\mathbb{Z}_q$. For each coordinate $i$, the score is $\mathrm{sc}_i=\sum_{j=1}^{J}M(K_je_i)$, summed as integers. Given a weight $h$, the candidate sets to $1$ the $h$ coordinates with the largest scores (ties broken by a fixed rule chosen by the user) and the others to $0$. The procedure outputs this candidate; checking it is a separate step (the residual test).

**Variant (SALSA, Algorithm 1).** The model reads integers encoded in base $B$, and inputs $Ke_i$ use integer values of $K$, five fixed and five random in $(q,10q)$, not reduced modulo $q$. For each $K$ the decoded outputs $p_i=M(Ke_i)$ are binarized by thresholding at their mean, at the mean after a softmax, or at their mode, in both orientations, giving six candidates per $K$. In the source's experiments candidates were compared with the known secret; without it, the residual test is used.

## Expansion

The method assumes that the model generalises to the special inputs $Ke_i$, which lie outside the training distribution; SALSA VERDE stops using it in large dimension for that reason. There is no correctness guarantee.

## Depends on

- [LWE with a prescribed secret distribution](../small-and-sparse-secret-lwe/lwe-with-a-secret-distribution.md)

## Proof depends on

None.

## Sources

- Cathy Yuanchen Li, Jana Sotáková, Emily Wenger, Mohamed Malhou, Evrard Garcelon, François Charton, Kristin Lauter, "SALSA PICANTE: a machine learning attack on LWE with binary secrets", ACM CCS 2023, https://doi.org/10.1145/3576915.3623076; numbers from arXiv:2303.04178v3, Section 4.3 (direct recovery).
- Emily Wenger, Mingjie Chen, François Charton, Kristin Lauter, "SALSA: Attacking Lattice Cryptography with Transformers", Advances in Neural Information Processing Systems 35 (NeurIPS 2022); numbers from arXiv:2207.04785v2, Section 4.3, Algorithm 1 and Appendix C.1.
- Cathy Yuanchen Li, Emily Wenger, Zeyuan Allen-Zhu, François Charton, Kristin Lauter, "SALSA VERDE: a machine learning attack on Learning With Errors with sparse small secrets", Advances in Neural Information Processing Systems 36 (NeurIPS 2023); numbers from arXiv:2306.11641v2, Section 2 (integer representation in $[0,q)$; secret recovery).
