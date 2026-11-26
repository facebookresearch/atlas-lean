# Lowe's attack on the Needham–Schroeder public-key protocol

**Theorem (Lowe).** The [Needham–Schroeder public-key protocol](needham-schroeder-public-key-protocol.md) guarantees neither authentication of the initiator to the
responder nor the secrecy of the responder's nonce. If an honest $A$ starts a session with a dishonest principal $C$, then $C$ can complete a session with $B$ in
which $B$ believes it talks to $A$, and learn $N_b$:

$$A \to C : \mathrm{aenc}(\langle A, N_a\rangle, \mathrm{pk}(C)), \quad C(A) \to B : \mathrm{aenc}(\langle A, N_a\rangle, \mathrm{pk}(B)), \quad B \to A : \mathrm{aenc}(\langle N_a, N_b\rangle, \mathrm{pk}(A)),$$

$$A \to C : \mathrm{aenc}(N_b, \mathrm{pk}(C)), \quad C(A) \to B : \mathrm{aenc}(N_b, \mathrm{pk}(B)),$$

where $C(A)$ denotes $C$ impersonating $A$: $A$ acts as a decryption oracle for $C$. With the identity of the responder added to message 2, $A$ would expect
$\langle N_a, \langle N_b, C\rangle\rangle$ and reject $B$'s reply, which blocks this attack.

## Depends on

- [The Needham–Schroeder public-key protocol](needham-schroeder-public-key-protocol.md)

## Sources

- V. Cortier and S. Kremer, "Formal models and techniques for analyzing security protocols: a tutorial", *Foundations and Trends in Programming Languages* 1(3), 2014, doi:10.1561/2500000001, copy at <https://inria.hal.science/hal-01090874>: Section 2.2, "Lowe's man in the middle attack", and Figure 2.2 (crediting G. Lowe, TACAS 1996).
