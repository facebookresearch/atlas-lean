# Distinguisher-based secret recovery for sparse LWE secrets

If $s_i=0$ then $(a+Ke_i)\cdot s=a\cdot s$, so a model that has learned the secret predicts nearly the same value on $a$ and $a+Ke_i$. Summing $|M(a)-M(a+Ke_i)|$ over test vectors scores coordinate $i$; the $h$ largest scores give a candidate support.

Let $s$ be a sparse secret and $M$ a model trained to predict $b$ from $a$ on (possibly reduced) pairs with secret $s$, whose outputs are read as integers in $[0,q)$. Let $a_1,\dots,a_T$ be test vectors. For each coordinate $i$,

$$
\mathrm{sc}_i=\sum_{t=1}^{T}\bigl|M(a_t)-M(a_t+K_te_i \bmod q)\bigr|,
$$

with $K_t$ drawn at random and the absolute difference taken between the integer outputs. Given $h$, the candidate support is the set of the $h$ coordinates with the largest scores (ties broken by a user-fixed rule).

**SALSA VERDE's choices.** $T=128$ held-out reduced vectors (same distribution as the training data) and $K_t$ uniform in $(0.3q,0.7q)$. For a binary secret the candidate sets the support to $1$. Since $h$ is unknown, it is tried over a range of values.

**SALSA PICANTE's choice.** Random test vectors $a_t$ with coordinates uniform in $[0,q)$; it compares $M(a+Ke_i)$ with $M(a)$ rather than with the true label as in SALSA's Algorithm 2.

The candidate is then checked by the residual test, which is not part of this procedure.

## Expansion

The identity $(a+Ke_i)\cdot s=a\cdot s+Ks_i$ is exact; that small scores indicate $s_i=0$ is a heuristic that depends on the trained model. For ternary secrets SALSA VERDE adds a separate two-bit procedure on the candidate support: if $s_i=s_j$, swapping $a_i$ and $a_j$, or replacing $(a_i,a_j)$ by $(a_i+c,a_j-c)$ with $c\ne0$, leaves $a\cdot s$ unchanged, and model predictions are compared to group the support into two classes, giving two sign assignments to verify; the source gives no explicit decision threshold for this grouping.

## Depends on

- [LWE with a prescribed secret distribution](../small-and-sparse-secret-lwe/lwe-with-a-secret-distribution.md)

## Proof depends on

None.

## Sources

- Cathy Yuanchen Li, Emily Wenger, Zeyuan Allen-Zhu, François Charton, Kristin Lauter, "SALSA VERDE: a machine learning attack on Learning With Errors with sparse small secrets", Advances in Neural Information Processing Systems 36 (NeurIPS 2023); numbers from arXiv:2306.11641v2, Section 2 (secret recovery) and Section 3 (partial and full recovery).
- Cathy Yuanchen Li, Jana Sotáková, Emily Wenger, Mohamed Malhou, Evrard Garcelon, François Charton, Kristin Lauter, "SALSA PICANTE: a machine learning attack on LWE with binary secrets", ACM CCS 2023, https://doi.org/10.1145/3576915.3623076; numbers from arXiv:2303.04178v3, Section 4.3 (distinguisher).
- Emily Wenger, Mingjie Chen, François Charton, Kristin Lauter, "SALSA: Attacking Lattice Cryptography with Transformers", Advances in Neural Information Processing Systems 35 (NeurIPS 2022); numbers from arXiv:2207.04785v2, Section 4.3, Algorithm 2 and Appendix C.2.
