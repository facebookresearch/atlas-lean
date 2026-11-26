# Split accumulation for an R1CS NARK from homomorphic commitments

For R1CS with matrices $A,B,C\in\mathbb{F}^{M\times N}$, instance $x\in\mathbb{F}^{n}$ and witness $w\in\mathbb{F}^{N-n}$, consider the NARK whose proof is $(C_A,C_B,C_C,w)$, with $C_A,C_B,C_C$ Pedersen commitments to $z_A=Az$, $z_B=Bz$, $z_C=Cz$ for $z=(x,w)$; the verifier reconstructs $z=(x,w)$, recomputes $z_A,z_B,z_C$, and checks $C_A=\mathsf{Commit}(z_A)$, $C_B=\mathsf{Commit}(z_B)$, $C_C=\mathsf{Commit}(z_C)$ and $C_C=\mathsf{Commit}(z_A\circ z_B)$. Split the verifier's input into the instance $(x,C_A,C_B,C_C)$ and the witness $w$. A split accumulator has instance part $(x,C_A,C_B,C_C,C_\circ)$, with a separate commitment $C_\circ$ to the Hadamard product, and witness part $w$; the decider recomputes $z_A,z_B,z_C$ from $z=(x,w)$ and checks the first three commitments together with $C_\circ=\mathsf{Commit}(z_A\circ z_B)$. To accumulate one predicate input into one old accumulator, the prover sends $\mathsf{pf}=\mathsf{Commit}(z_A\circ z'_B+z'_A\circ z_B)$, where unprimed vectors come from the input and primed ones from the old accumulator, a random-oracle challenge $\beta$ is derived, the instance parts are combined as $\mathsf{acc}+\beta\cdot q$ on $x,C_A,C_B,C_C$, and $C_\circ$ is updated to $C_\circ+\beta\,\mathsf{pf}+\beta^{2}C_C$, with the witnesses combined in the same way. In the random oracle model and under the hardness of discrete logarithms this is a split accumulation scheme whose accumulation verifier makes one random-oracle call, $O(n)$ field operations and four group scalar multiplications (three if $C_A$ and $C_B$ are merged). This one-old, one-new case suffices for IVC; PCD needs $m$ old accumulators and $n$ inputs, for which the multi-input construction adds a subprotocol for accumulating Hadamard products. The compiler from NARKs with split accumulation to PCD holds in the standard model, so applying it here requires heuristically instantiating the random oracle.

## Proof sketch

The decider's linear checks are preserved by random linear combinations because Pedersen commitments are homomorphic. For the Hadamard check, $(z'_A+\beta z_A)\circ(z'_B+\beta z_B)$ is a degree-two polynomial in $\beta$ whose coefficients are $z'_A\circ z'_B$, committed in the old $C_\circ$, the cross term committed in $\mathsf{pf}$, and $z_A\circ z_B$, which equals $z_C$ for a valid input. Knowledge soundness forks the random oracle to obtain three accepting accumulations with distinct $\beta$, interpolates, and uses binding of Pedersen commitments, which reduces to discrete logarithms.

## Depends on

- [Split accumulation and NARKs with accumulation](../incrementally-verifiable-computation-and-pcd/split-accumulation.md)
- [Rank-1 constraint systems](../relaxed-r1cs-folding-schemes/rank-one-constraint-system.md)
- [Pedersen commitment scheme](../commitment-schemes/pedersen-commitments-perfect-hiding-and-binding/scheme.md)
- [Discrete-logarithm experiment](../../public-key/hardness-assumptions/dlog-game.md)
- [The random oracle model](../../public-key/random-oracle-constructions/the-random-oracle-model.md)
- [Proof-carrying data for a compliance predicate](../incrementally-verifiable-computation-and-pcd/pcd-scheme.md)

## Proof depends on

- [Proof-carrying data from NARKs with split accumulation](../incrementally-verifiable-computation-and-pcd/pcd-from-accumulation.md)

## Sources

- Benedikt Bünz, Alessandro Chiesa, William Lin, Pratyush Mishra, Nicholas Spooner, "Proof-Carrying Data without Succinct Arguments", CRYPTO (2021), IACR ePrint 2020/1618, Theorems 1 and 2, Sections 2.3.1 to 2.3.3, and Section 8 (the multi-input construction).
