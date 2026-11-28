# Random-oracle programming at high-min-entropy points

In the Fiat–Shamir signature scheme derived from a Sigma protocol $(P, V)$ with $\delta$-unpredictable commitments (every fixed commitment $\hat t$ occurs with probability at most $\delta$ in an honest interaction; Boneh and Shoup, Definition 19.7), let an adversary make at most $Q_s$ signing queries and at most $Q_{\mathrm{ro}}$ explicit random-oracle queries (extended by one if needed so the forgery message–commitment pair is queried). Compare Game 0 (the unprogrammed random-oracle signing game, in which each signing query uses the oracle's existing value at $(m_i, t_i)$ if already defined and otherwise sets it to a fresh uniform challenge) with Game 1 (the programmed game, in which each signing query overwrites the oracle at $(m_i, t_i)$ with a fresh uniform challenge regardless of whether that point was already defined). The two games agree until a signing query's commitment hits an already-defined oracle point, so by the difference lemma their winning-event probabilities satisfy

$$
|\Pr[W_1] - \Pr[W_0]| \le Q_s(Q_s + Q_{\mathrm{ro}} + 1)\delta
$$

(Boneh and Shoup, proof of Theorem 19.7 for Schnorr with $\delta = 1/q$, carried over verbatim to $\delta$-unpredictable commitments in Theorem 19.16).

## Proof sketch

On the $i$-th signing query, at most $Q_s + Q_{\mathrm{ro}} + 1$ oracle points have been defined (by explicit adversary queries or earlier signing queries) before the fresh commitment $t_i$ is drawn. Since $t_i$ has guessing probability at most $\delta$, a union bound over the already-defined points bounds the collision probability at query $i$ by $(Q_s + Q_{\mathrm{ro}} + 1)\delta$, and summing over $i = 1, \dots, Q_s$ gives $Q_s(Q_s + Q_{\mathrm{ro}} + 1)\delta$; until such a collision occurs, the programmed and unprogrammed games are identically distributed, so the difference lemma yields $|\Pr[W_1] - \Pr[W_0]| \le Q_s(Q_s + Q_{\mathrm{ro}} + 1)\delta$. More generally (derived directly by the same argument, not stated as a standalone theorem in the cited sources), any oracle handler making at most $T$ programming writes at fresh $\delta$-unpredictable points $\pi(\tau)$ alongside at most $H$ other oracle queries has total collision probability at most $T H \delta + \binom{T}{2}\delta \le T(H + T)\delta$ against the unprogrammed experiment that reads the oracle's value at $\pi(\tau)$ (not against an experiment that erases the writes, which can differ by almost $1$ when handler outputs expose programmed points).

## Depends on

- [The random oracle model](../../public-key/random-oracle-constructions/the-random-oracle-model.md)
- [Guessing probability, min-entropy and collision probability](../../randomness-extraction/guessing-probability-min-entropy-and-collision.md)
- [A Sigma protocol](../../signatures-and-protocols/zero-knowledge-proofs/sigma-protocol.md)
- [Fiat–Shamir signatures from Sigma protocols are EUF-CMA secure in the random oracle model](../../signatures-and-protocols/sigma-protocols-and-fiat-shamir/identification-and-fiat-shamir/fiat-shamir-signatures.md)
- [Signature schemes and (strong) unforgeability in the random oracle model](../../signatures-and-protocols/sigma-protocols-and-fiat-shamir/random-oracle-signatures/rom-signature-unforgeability.md)
- [The difference lemma](../games-and-advantages/advantage-le-win-prob-of-eq-of-not-bad.md)

## Proof depends on

- [Effect of overwriting one entry of a memoized random oracle](overwritten-random-oracle-entry.md)
- [Accumulated bad-event probability over a query-bounded run](accumulated-bad-event-probability.md)
- [Fundamental lemma of game playing for stateful oracle handlers](fundamental-lemma-for-stateful-handlers.md)

## Sources

- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023, Definition 19.7 ($\delta$-unpredictable commitments), Theorem 19.7 and its proof (Game 0 to Game 1 difference-lemma step $|\Pr[W_1] - \Pr[W_0]| \le Q_s(Q_s + Q_{\mathrm{ro}} + 1)/q$), and Theorem 19.16 (generalizing the same proof to $\delta$-unpredictable commitments with collision term $Q_s(Q_s + Q_{\mathrm{ro}} + 1)\delta$).
- M. Bellare and P. Rogaway, "Random Oracles are Practical: A Paradigm for Designing Efficient Protocols", Proceedings of the 1st ACM Conference on Computer and Communications Security (CCS), 1993.
