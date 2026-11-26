# SuperNova: NIVC with per-instruction prover cost

Assuming a folding scheme for committed relaxed R1CS (with an additively homomorphic binding commitment), in the random oracle model there is an NIVC scheme for any functions $F_1,\dots,F_k$ and selector $\phi$ in which the prover maintains $k$ running relaxed R1CS instances, one per function, and at step $i$ folds the fresh instance only into the running instance of the selected function $F_{\phi(z_i,w_i)}$. The per-step prover cost is proportional to the size of the selected $F_j$ plus a recursion overhead independent of $k$ except for hashing the $k$ running instances, and the final proof consists of the $k$ running instances (compressible by a SNARK).

## Proof sketch

The augmented circuit for $F_j$ checks the program counter, folds the incoming fresh instance into the $j$-th running instance and updates a commitment to all running instances. Knowledge soundness follows from Nova's argument applied to each running chain, using the program-counter consistency to stitch together the executed sequence of instructions.

## Depends on

- [Non-uniform incrementally verifiable computation](non-uniform-ivc.md)
- [Nova: IVC with constant recursion overhead from folding](../relaxed-r1cs-folding-schemes/nova-ivc.md)

## Proof depends on

- [Non-interactive folding via Fiat–Shamir in the random oracle model](../relaxed-r1cs-folding-schemes/nova-nifs.md)
- [Nova's folding scheme for committed relaxed R1CS](../relaxed-r1cs-folding-schemes/nova-folding-theorem.md)

## Sources

- Abhiram Kothapalli, Srinath Setty, "SuperNova: Proving Universal Machine Executions without Universal Circuits", IACR ePrint 2022/1758 (2022).
