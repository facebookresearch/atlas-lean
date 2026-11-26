# Uniform correctness for a circuit class

There is a single negligible function $\varepsilon$ of the security parameter with the following property. At each $\lambda$, choose any input arity $t$ and any admitted $t$-input circuit $C$. For every generated key pair, message tuple and tuple of supported fresh ciphertexts, the probability of rejection or decryption to the wrong value after evaluation is at most $\varepsilon(\lambda)$. Only evaluation is randomized in this probability.

The same bound works even if the choice of circuit changes with $\lambda$. [Fixed-circuit correctness](fixed-circuit-correct.md) instead allows a separate negligible bound for each circuit. For example, an error of one at arity $\lambda+1$ and zero at every other arity eventually vanishes for each fixed circuit but not uniformly over arities.

Gentry, *A Fully Homomorphic Encryption Scheme* (2009), Definition 2.1.1 (printed p. 28, PDF p. 38), specifies the inputs and the source of randomness but does not write an explicit negligible majorant. Uniformity across admitted circuits is the convention used here for compact, full and leveled evaluation. Definition 5.2.4 (printed p. 60, PDF p. 70) makes the arity depend on the circuit, without choosing the order of the negligible bound.
