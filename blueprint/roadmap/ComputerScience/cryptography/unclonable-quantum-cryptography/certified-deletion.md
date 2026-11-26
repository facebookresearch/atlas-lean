# Encryption with certified deletion

A (public- or secret-key) encryption scheme with *certified deletion* has, in addition to encryption and decryption, an algorithm $\mathsf{Del}(\mathsf{ct})\to\mathsf{cert}$ that destroys a quantum ciphertext and outputs a classical certificate, and a verification $\mathsf{Vrfy}(\mathsf{vk},\mathsf{cert})$ using information kept by the encryptor. Security is not stated conditioned on acceptance: an adversary may make acceptance negligibly likely, and the normalized state conditioned on that rare event need not hide anything. Instead, the accept decision is part of the event or the output. In the one-time secret-key version (Broadbent–Islam), an adversary $(\mathcal{A}_0,\mathcal{A}_1,\mathcal{A}_2)$ chooses a message $\mathsf{msg}_0$, $\mathcal{A}_1$ receives an encryption of $\mathsf{msg}_0$ ($b=1$) or of $0^{n}$ ($b=0$) and outputs a certificate, the key is then given to $\mathcal{A}_2$, which outputs $b'$, and security requires $|p_0-p_1|\le\eta(\lambda)$ for a negligible $\eta$, where $p_b=\Pr[b'=1\wedge\mathsf{Vrfy}\text{ accepts}]$ in the game with challenge $b$. In the everlasting version (Bartusek–Khurana), a QPT adversary receives an encryption of $b$ and outputs a certificate and a residual state; the experiment outputs the residual state if $\mathsf{Vrfy}(\mathsf{vk},\mathsf{cert})$ accepts and a symbol $\bot$ otherwise, and the two output distributions for $b=0,1$ must be within negligible trace distance (so the residual state hides $b$ even from a later computationally unbounded distinguisher); in addition, the adversary's final output together with the verification bit must computationally hide $b$.

## Depends on

- [Indistinguishability of encryptions with error $\varepsilon$](../security-games/semantic-security-and-indistinguishability/ind-secure.md)
- [Wiesner's private-key quantum money](wiesner-quantum-money.md)

## Sources

- Anne Broadbent, Rabib Islam, "Quantum Encryption with Certified Deletion", TCC (2020).
- James Bartusek, Dakshita Khurana, "Cryptography with Certified Deletion", CRYPTO (2023), arXiv:2207.01754.
