# Gate bootstrapping: FHE for Boolean circuits with one bootstrap per gate

Encode bits as TLWE messages in $\{\pm 1/8\}$. For any binary gate among NAND, AND, OR, XOR (and their negations), the sum of the two input samples plus a public constant has phase in $(-1/4,1/4)$ or its complement depending on the gate output; one programmable bootstrapping with the sign function $x\mapsto\pm 1/8$ (negacyclic) refreshes the output to a fresh encoding. Assuming LWE-type hardness of TLWE/TRLWE and circular security of the bootstrapping keys, this yields a fully homomorphic encryption scheme for Boolean circuits of unbounded depth, with one bootstrapping per gate whose parameters are independent of circuit depth.

## Proof sketch

If input errors are below $1/16$ in absolute value, the linear combination's phase lies in the correct half-interval, and bootstrapping maps it to the correct output with fresh error, which by parameter choice is again below $1/16$. Induction on circuit depth gives correctness; security reduces to TLWE/TRLWE for ciphertexts and requires circular security for the keys (as in Gentry's bootstrapping theorem).

## Depends on

- [Programmable bootstrapping in TFHE](programmable-bootstrapping.md)
- [Gentry's bootstrapping theorem](../gentry-s-bootstrapping-theorem.md)

## Proof depends on

- [Programmable bootstrapping in TFHE](programmable-bootstrapping.md)
- [Gentry's bootstrapping theorem](../gentry-s-bootstrapping-theorem.md)

## Sources

- Ilaria Chillotti, Nicolas Gama, Mariya Georgieva, Malika Izabachène, "TFHE: Fast Fully Homomorphic Encryption over the Torus", Journal of Cryptology (2020), IACR ePrint 2018/421.
