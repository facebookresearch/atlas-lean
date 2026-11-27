# Universal composition with joint state and multi-session composition

Let $\hat{\mathcal{F}}$ be the *multi-session extension* of an ideal functionality $\mathcal{F}$, which runs independent copies of $\mathcal{F}$ indexed by sub-session identifiers (created lazily on first use). If a single protocol instance $\hat\rho$ UC-realizes $\hat{\mathcal{F}}$, and $\pi$ is a protocol in the $\mathcal{F}$-hybrid model using many instances of $\mathcal{F}$, then the *joint-state composition* $\pi^{[\hat\rho]}$, which replaces all instances of $\mathcal{F}$ by sub-sessions of one instance of $\hat\rho$, UC-emulates $\pi$ in the $\mathcal{F}$-hybrid model. Quantitatively, for a fixed family of $m$ sessions, composition multiplies the simulator overhead by at most $m$ and adds the per-session errors, and replacing the private resource of a hybrid functionality by one that emulates it is a state-separating reduction with the same advantage.

## Proof sketch

Translate calls of $\pi$ to sub-session calls of $\hat{\mathcal{F}}$ (the protocol $\tilde\pi$ in the $\hat{\mathcal{F}}$-hybrid model emulates $\pi$ exactly), then apply the composition theorem to replace $\hat{\mathcal{F}}$ by $\hat\rho$.

## Depends on

- [UC emulation](../uc-emulation.md)

## Proof depends on

- [Universal composition theorem](../universal-composition-theorem.md)
- [Completeness of the dummy adversary](uc-dummy-adversary.md)
- [Reduction, hybrid and state-simulation lemmas for packages](../../../security-games/state-separating-proofs/ssp-reduction-and-hybrid-lemmas.md)

## Sources

- Ran Canetti and Tal Rabin, "Universal Composition with Joint State", Advances in Cryptology – CRYPTO 2003, 2003.
- Ran Canetti, "Universally Composable Security", Journal of the ACM, 2020.
