# Homomorphic encryption: correctness and compactness

A homomorphic encryption scheme $\mathcal{E}$ consists of key generation, encryption, decryption and an evaluation algorithm $\mathrm{Evaluate}(pk, C, \Psi)$ for
circuits $C$ in a class $\mathcal{C}_\mathcal{E}$, where $\lambda$ is the security parameter.

- $\mathcal{E}$ is *correct* for circuits in $\mathcal{C}_\mathcal{E}$ if for every key pair $(sk, pk)$ output by key generation, every $C \in \mathcal{C}_\mathcal{E}$ with $t$ inputs, all
  plaintexts $\pi_1, \dots, \pi_t$ and all ciphertexts $\Psi = (\psi_1, \dots, \psi_t)$ with $\psi_i \leftarrow \mathrm{Encrypt}(pk, \pi_i)$, the ciphertext $\psi \leftarrow \mathrm{Evaluate}(pk, C, \Psi)$
  decrypts to $C(\pi_1, \dots, \pi_t)$, except with negligible probability over the coins of $\mathrm{Evaluate}$.
- $\mathcal{E}$ is *compact* if there is a polynomial $f$ such that for every $\lambda$ its decryption algorithm is computed by a circuit $D_\mathcal{E}$ of size at most $f(\lambda)$.
- $\mathcal{E}$ *compactly evaluates* the circuits in $\mathcal{C}_\mathcal{E}$ if it is compact and correct for them, and it is *fully homomorphic* if it compactly evaluates all
  circuits.
- A family $\{\mathcal{E}^{(d)} : d \in \mathbb{Z}^+\}$ is *leveled fully homomorphic* if all $\mathcal{E}^{(d)}$ use the same decryption circuit, $\mathcal{E}^{(d)}$ compactly evaluates all
  circuits of depth at most $d$ over a specified set of gates, and the algorithms of $\mathcal{E}^{(d)}$ run in time polynomial in $\lambda$, $d$ and, for
  $\mathrm{Evaluate}$, the size of the circuit.

Compactness bounds the decryption circuit, and hence the length of evaluated ciphertexts, independently of the evaluated circuit; without it the
trivial scheme whose evaluation outputs $(C, \Psi)$ would be correct.

## Depends on

- [Public-key encryption scheme](../../security-games/generic-security-games/pkescheme.md)

## Sources

- C. Gentry, *A fully homomorphic encryption scheme*, PhD thesis, Stanford University, 2009, <https://crypto.stanford.edu/craig/craig-thesis.pdf>: Section 2.1, Definitions 2.1.1–2.1.5 and the remark on trivial schemes before Definition 2.1.2.
