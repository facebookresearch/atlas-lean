# Simulating the encryption oracle from the public key

Let $E(pk, m, \rho)$ be a ciphertext computed deterministically from a public key, a message and
coins $\rho$ in a finite nonempty set $R$. From a chosen-plaintext adversary $A$ with an encryption
oracle and a number $n$, the simulating eavesdropper draws the coins of $A$ together with uniform
coins $\rho_1, \dots, \rho_n$ and $\rho'_1, \dots, \rho'_n$ in $R$. It runs $A$ without an oracle,
answering, for $i \le n$, the $i$-th query $m$ of the first stage with $E(pk, m, \rho_i)$ and the
$i$-th query $m$ of the second stage with $E(pk, m, \rho'_i)$ (Katz and Lindell, proof of
Proposition 11.3). Every query $m$ after the $n$-th of a stage is answered with $E(pk, m, \rho_0)$
for one fixed coin $\rho_0 \in R$.
