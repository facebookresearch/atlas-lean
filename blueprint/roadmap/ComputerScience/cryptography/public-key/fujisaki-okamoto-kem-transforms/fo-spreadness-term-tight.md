# The spreadness term of $\mathrm{FO}^{\perp}$ is tight

In the proof of IND-CCA security of $\mathrm{FO}^{\perp}$, the step that replaces real decapsulation by a keyless simulator must lose an additive term of order $q_D 2^{-\gamma}$: for a uniform message sampler on a finite $M$ and every $\gamma$, there is a $\gamma$-spread PKE and a one-query adversary whose distinguishing advantage between the real and the simulated decapsulation oracle is at least $2^{-\gamma}$ minus a term of order $1/|M|$. Hence the spreadness hypothesis cannot be dropped from the $\mathrm{FO}^{\perp}$ bound.

## Proof sketch

The adversary guesses a message and fresh coins, forms a ciphertext without querying $G$, and submits it for decapsulation; with probability about $2^{-\gamma}$ the guess agrees with $G$'s answer, in which case the real oracle accepts while the simulator, which only knows queried points, rejects.

## Depends on

- [The KEM transforms $U^{\perp}$ and $U^{\not\perp}$ and the Fujisaki–Okamoto KEMs](transforms-u-and-fo-kems.md)
- [Public-key encryption with explicit coins, $\delta$-correctness and $\gamma$-spreadness](pke-with-explicit-coins.md)

## Proof depends on

- [IND-CCA security of $\mathrm{FO}^{\perp}$ in the random oracle model](fo-explicit-rejection-ind-cca.md)

## Sources

- Dennis Hofheinz, Kathrin Hövelmanns and Eike Kiltz, "A Modular Analysis of the Fujisaki–Okamoto Transformation", Theory of Cryptography (TCC 2017), 2017.
