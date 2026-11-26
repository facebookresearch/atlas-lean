# The spreadness term of $\mathrm{FO}^{\perp}$ is tight

In the proof of IND-CCA security of $\mathrm{FO}^{\perp}$, the step that replaces real decapsulation by a keyless simulator cannot be lossless: for a uniform message sampler on a finite $M$ and every integer $\gamma \ge 1$, there is a perfectly correct $\gamma$-spread PKE and a one-query adversary whose distinguishing advantage between the real and the simulated decapsulation oracle is at least $2^{-\gamma} - 1/|M|$. Hence the spreadness hypothesis cannot be dropped from the $\mathrm{FO}^{\perp}$ bound.

## Proof sketch

The adversary guesses a message and fresh coins, forms a ciphertext without querying $G$, and submits it for decapsulation; for a PKE in which every ciphertext of $\mathrm{Enc}(pk, m; \cdot)$ has probability exactly $2^{-\gamma}$, the guess agrees with $G$'s answer with probability $2^{-\gamma}$, in which case the real oracle accepts, while the simulator, which only knows queried points, accepts only if the guessed message is the challenge message, which has probability at most $1/|M|$.

## Depends on

- [The KEM transforms $U^{\perp}$ and $U^{\not\perp}$ and the Fujisaki–Okamoto KEMs](transforms-u-and-fo-kems.md)
- [Public-key encryption with explicit coins, $\delta$-correctness and $\gamma$-spreadness](pke-with-explicit-coins.md)

## Proof depends on

- [IND-CCA security of $\mathrm{FO}^{\perp}$ in the random oracle model](fo-explicit-rejection-ind-cca.md)

## Sources

- Dennis Hofheinz, Kathrin Hövelmanns and Eike Kiltz, "A Modular Analysis of the Fujisaki–Okamoto Transformation", Theory of Cryptography (TCC 2017), 2017.
