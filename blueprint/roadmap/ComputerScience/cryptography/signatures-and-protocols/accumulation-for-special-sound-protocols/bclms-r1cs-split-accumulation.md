# Split accumulation for an R1CS NARK from homomorphic commitments

Let the NARK for R1CS have proofs consisting of homomorphic (e.g., Pedersen) commitments to the vectors $Az$, $Bz$, $Cz$ and $z$, with the verifier checking the R1CS relation in the clear on the opened vectors. Under the discrete logarithm assumption in the random oracle model, this NARK has a split accumulation scheme whose accumulation verifier performs a constant number of group scalar multiplications, and the resulting PCD (via the compiler from NARKs with split accumulation) is built from the discrete logarithm assumption without any succinct argument.

## Proof sketch

Accumulate the bilinear check $Az\circ Bz=Cz$ by random linear combination with a cross term, as in relaxed R1CS: the accumulator carries the combined commitments plus a committed error. The verifier combines commitments homomorphically; the decider opens the final commitments and checks the relaxed relation. Soundness reduces to binding of Pedersen commitments, hence to discrete logarithms.

## Depends on

- [Split accumulation and NARKs with accumulation](../incrementally-verifiable-computation-and-pcd/split-accumulation.md)
- [Relaxed R1CS instances with slack vector and scalar](../relaxed-r1cs-folding-schemes/relaxed-r1cs.md)
- [Pedersen commitment scheme](../commitment-schemes/pedersen-commitments-perfect-hiding-and-binding/scheme.md)
- [Discrete-logarithm experiment](../../public-key/hardness-assumptions/dlog-game.md)

## Proof depends on

- [Cross-term identity for folding relaxed R1CS](../relaxed-r1cs-folding-schemes/nova-cross-term.md)
- [Proof-carrying data from NARKs with split accumulation](../incrementally-verifiable-computation-and-pcd/pcd-from-accumulation.md)

## Sources

- Benedikt Bünz, Alessandro Chiesa, William Lin, Pratyush Mishra, Nicholas Spooner, "Proof-Carrying Data without Succinct Arguments", CRYPTO (2021), IACR ePrint 2020/1618.
