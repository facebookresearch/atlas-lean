# Nova: IVC with constant recursion overhead from folding

Let $F$ be a step function and $\mathsf{NIFS}$ the non-interactive folding scheme for committed relaxed R1CS. Define the augmented step circuit $F'$ which, on input a running instance $U_i$, a fresh instance $u_i$ and the cross-term commitment, checks that $u_i$'s public output hashes the previous state, runs the $\mathsf{NIFS}$ verifier to obtain $U_{i+1}$, computes $z_{i+1}=F(z_i,w_i)$, and outputs a hash of $(i+1,z_0,z_{i+1},U_{i+1})$. The resulting IVC scheme, whose proof is a pair (running relaxed instance-witness, fresh instance-witness), is complete and knowledge sound in the random oracle model when the oracle is instantiated by a hash computed inside $F'$ (heuristic step). Its recursion overhead is constant: $F'$ adds to $F$ only the NIFS verifier, dominated by two group scalar multiplications, and the prover's work per step is dominated by two multi-exponentiations of size $O(|F|)$.

## Proof sketch

Completeness follows inductively from completeness of folding. For knowledge soundness, from a valid final pair extract by NIFS knowledge soundness a satisfying running instance and fresh instance for the previous step, whose satisfaction in $F'$ certifies the previous step of $F$; iterate. Since folding extraction is linear rather than polynomial-blowup, extraction succeeds for polynomially many steps in the random oracle model.

## Depends on

- [Non-interactive folding via Fiat–Shamir in the random oracle model](nova-nifs.md)
- [Incrementally verifiable computation scheme for an iterated function](../incrementally-verifiable-computation-and-pcd/ivc-scheme.md)
- [Relaxed R1CS instances with slack vector and scalar](relaxed-r1cs.md)
- [The random oracle model](../../public-key/random-oracle-constructions/the-random-oracle-model.md)

## Proof depends on

- [Nova's folding scheme for committed relaxed R1CS](nova-folding-theorem.md)

## Sources

- Abhiram Kothapalli, Srinath Setty, Ioanna Tzialla, "Nova: Recursive Zero-Knowledge Arguments from Folding Schemes", CRYPTO (2022), IACR ePrint 2021/370.
