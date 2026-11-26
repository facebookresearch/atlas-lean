# Homomorphic evaluation of Boolean circuits layer by layer along a key chain

Let $\mathcal{E}$ be bootstrappable for the identity and NAND gates. Compile a Boolean circuit $C$ of depth $d$ into $2d$ consecutive layers of NAND gates and copy (identity) gates by De Morgan's laws. Given a valid acyclic key chain of length at least $2d$, evaluate layer $i$ by applying refresh or NAND refresh with link $\overline{sk_{i-1}}$ to the ciphertexts of layer $i-1$, and encrypt constants under the current public key. Then every output wire decrypts under $sk_{2d}$ to the corresponding output of $C$ on the plaintext inputs, every ciphertext has the base width, the order and multiplicities of the selected output wires are preserved, and unused gates do not increase the number of key transitions.

## Proof sketch

Induct over the layers with the invariant that each wire of layer $i$ is a well-sized ciphertext under $pk_i$ decrypting to the wire value; the inductive step is the correctness of refresh and NAND refresh.

## Depends on

- [Acyclic chains of encrypted secret keys](encrypted-key-chains.md)
- [Gentry's refresh (recryption) algorithm](refresh-algorithm.md)

## Proof depends on

- [Correctness of refresh and NAND refresh](refresh-correctness.md)

## Sources

- Craig Gentry, "Fully Homomorphic Encryption Using Ideal Lattices", Proceedings of the Forty-First Annual ACM Symposium on Theory of Computing, 2009.
