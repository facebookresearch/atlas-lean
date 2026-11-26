# The quantum one-time pad

Alice and Bob share a uniform key $(a, b) \in \{0,1\}^n \times \{0,1\}^n$. To send an $n$-qubit state $\rho$, Alice sends $X^a Z^b \rho\, (X^a Z^b)^\dagger$, where $X^a Z^b$ is the Pauli string applying $X$ on the qubits with $a_i = 1$ and $Z$ on those with $b_i = 1$; Bob decrypts by applying $(X^a Z^b)^\dagger$. Decryption recovers $\rho$ for every key, and the average ciphertext over the key is the maximally mixed state,

$$
\frac{1}{4^n}\sum_{a, b} X^a Z^b\,\rho\,(X^a Z^b)^\dagger = \frac{I}{2^n},
$$

for every state $\rho$; hence the eavesdropper's state is independent of the plaintext (a private quantum channel).

## Proof sketch

The $4^n$ Pauli strings form an orthogonal basis of the operators on $n$ qubits; averaging the conjugation by all of them is the completely depolarizing channel, which sends every density operator to $I/2^n$.

## Depends on

- [Characterizations of perfect security](perfect-security-characterizations.md)

## Sources

- Andris Ambainis, Michele Mosca, Alain Tapp and Ronald de Wolf, "Private Quantum Channels", 41st Annual Symposium on Foundations of Computer Science (FOCS 2000), 2000.
