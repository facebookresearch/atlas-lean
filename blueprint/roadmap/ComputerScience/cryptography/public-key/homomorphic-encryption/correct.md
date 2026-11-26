# Correct

Fix an input arity $t$ and a single-output circuit $C$ of that arity. There is a negligible function $\varepsilon_C$ of the security parameter with the following property. For every $\lambda$ at which $C$ is permitted, fix any generated key pair, any $t$ messages and any tuple of ciphertexts in the respective supports of their fresh encryptions. The probability that the evaluated ciphertext decrypts to a different message from the output of $C$, or is rejected, is at most $\varepsilon_C(\lambda)$. Only the evaluator's coins are sampled. The bound can depend on the circuit but not on the choice of keys, messages or fresh ciphertexts.

This is the circuit-wise reading of Gentry, *A Fully Homomorphic Encryption Scheme* (2009), Definition 2.1.1 (printed p. 28, PDF p. 38). Definition 5.2.4 (printed p. 60, PDF p. 70) also treats the arity as depending on the circuit.
