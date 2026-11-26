# Frege-type systems are not automatable under cryptographic assumptions

If factoring Blum integers is hard for polynomial-size circuits, then $\mathrm{TC}^0$-Frege does not have feasible interpolation and hence is not automatable (Bonet-Pitassi-Raz). If the RSA function is secure, then Extended Frege is not automatable (Krajíček-Pudlák). If the Diffie-Hellman function cannot be computed by circuits of size $2^{n^{\varepsilon}}$ for some $\varepsilon > 0$, then bounded-depth Frege of sufficiently large constant depth does not have feasible interpolation and hence is not automatable (Bonet-Domingo-Gavaldà-Maciel-Pitassi).

## Proof sketch

Encode a one-way permutation-based bit commitment or key-agreement protocol as a split CNF $A(x, y) \wedge B(x, z)$ where $x$ is the public transcript: one side asserts the secret bit is $0$, the other that it is $1$. The system has short refutations because it can prove the uniqueness of the hidden bit, while feasible interpolation would compute the hidden bit from the public transcript, breaking the cryptographic assumption.

## Depends on

- [Automatability implies feasible interpolation for systems closed under restriction](automatability-implies-interpolation.md)
- [Automatable proof systems](automatable-proof-system.md)

## Sources

- M. L. Bonet, T. Pitassi, R. Raz, "On interpolation and automatization for Frege systems", SIAM Journal on Computing 29 (2000) 1939-1967.
- J. Krajíček, P. Pudlák, "Some consequences of cryptographical conjectures for S^1_2 and EF", Information and Computation 140 (1998) 82-94.
- M. L. Bonet, C. Domingo, R. Gavaldà, A. Maciel, T. Pitassi, "Non-automatizability of bounded-depth Frege proofs", Computational Complexity 13 (2004) 47-68.
