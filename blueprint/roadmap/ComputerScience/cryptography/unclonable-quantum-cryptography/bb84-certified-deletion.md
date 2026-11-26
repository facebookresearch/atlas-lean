# Information-theoretic certified deletion from BB84 states

The secret-key scheme that encodes the key bits of a one-time pad in BB84 states $|x\rangle_\theta$ (computational-basis positions carry the pad, Hadamard-basis positions serve as deletion checks), where deletion measures all qubits in the Hadamard basis and the certificate is accepted if it agrees with $x$ on the Hadamard positions, satisfies certified deletion with security error exponentially small in $n$: conditioned on an accepted certificate, the adversary's information about the message is negligible even after the key (including $\theta$) is revealed.

## Proof sketch

Accepting certificates require Hadamard-basis outcomes consistent with $x$ on the check positions; by an entropic uncertainty relation (or the monogamy argument), passing the check implies high min-entropy of the computational-basis values of the pad positions given the adversary's state, and privacy amplification with a universal hash extracts a pad that is close to uniform.

## Depends on

- [Encryption with certified deletion](certified-deletion.md)

## Proof depends on

- [Leftover hash lemma](../randomness-extraction/leftover-hash-lemma.md)

## Sources

- Anne Broadbent, Rabib Islam, "Quantum Encryption with Certified Deletion", TCC (2020).
