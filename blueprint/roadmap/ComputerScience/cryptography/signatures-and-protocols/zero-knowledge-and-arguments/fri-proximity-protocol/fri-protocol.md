# The FRI protocol

The *Fast Reed–Solomon IOP of proximity* (FRI) tests that a word $f^{(0)} : D_0 \to \mathbb{F}$ on a smooth domain $|D_0| = 2^d$ is close to $\mathrm{RS}[\mathbb{F}, D_0, \rho]$. In the commit phase, for rounds $i = 0, \dots, m-1$ with folding arities $l^{(i)} = 2^{s_i} \ge 2$, the verifier sends a uniform $z_i$ and the prover sends an oracle $f^{(i+1)}$ on $D_{i+1} = D_i^{l^{(i)}}$ claimed to equal $\mathrm{Fold}(f^{(i)}, z_i)$; finally the prover sends the last word, which must be a low-degree codeword. In the query phase the verifier samples a starting point in $D_0$, reads the fiber above it in every round, and checks that each fold is consistent with the next oracle. Binary (2-to-1) FRI is the case $l^{(i)} = 2$. In *batched* FRI, a batch of words $f_1, \dots, f_t$ is first combined as $\sum_j \lambda_j f_j$ (or $\sum_j \lambda^j f_j$) with verifier randomness.

## Depends on

- [Reed–Solomon folding over multiplicative cosets](reed-solomon-coset-folding.md)
- [Public-coin interactive oracle proofs](../interactive-oracle-proofs/public-coin-iop.md)

## Sources

- Eli Ben-Sasson, Iddo Bentov, Yinon Horesh and Michael Riabzev, "Fast Reed–Solomon Interactive Oracle Proofs of Proximity", 45th International Colloquium on Automata, Languages, and Programming (ICALP 2018), 2018.
- Eli Ben-Sasson et al., "Proximity Gaps for Reed–Solomon Codes", Journal of the ACM, 2023.
