# Universal composition with joint state and multi-session composition

Let $\hat{\mathcal{F}}$ be the *multi-session extension* of an ideal functionality $\mathcal{F}$, which runs independent copies of $\mathcal{F}$ indexed by sub-session identifiers (created lazily on first use). If a single protocol instance $\hat\rho$ UC-realizes $\hat{\mathcal{F}}$, and $\pi$ is a protocol in the $\mathcal{F}$-hybrid model using many instances of $\mathcal{F}$, then the *joint-state composition* $\pi^{[\hat\rho]}$, which replaces all instances of $\mathcal{F}$ by sub-sessions of one instance of $\hat\rho$, UC-emulates $\pi$ in the $\mathcal{F}$-hybrid model (Canetti and Rabin, Theorem 1).

## Proof sketch

Translate calls of $\pi$ to sub-session calls of $\hat{\mathcal{F}}$ (the protocol $\tilde\pi$ in the $\hat{\mathcal{F}}$-hybrid model emulates $\pi$ exactly), then apply the composition theorem to replace $\hat{\mathcal{F}}$ by $\hat\rho$.

## Depends on

- [UC emulation](../uc-emulation.md)

## Proof depends on

- [Universal composition theorem](../universal-composition-theorem.md)
- [Completeness of the dummy adversary](uc-dummy-adversary.md)

## Sources

- Ran Canetti and Tal Rabin, "Universal Composition with Joint State", Advances in Cryptology – CRYPTO 2003, 2003, Theorem 1.
- Ran Canetti, "Universally Composable Security", Journal of the ACM, 2020.
