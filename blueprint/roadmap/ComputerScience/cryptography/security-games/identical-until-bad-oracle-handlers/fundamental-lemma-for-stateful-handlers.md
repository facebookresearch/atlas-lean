# Fundamental lemma of game playing for stateful oracle handlers

Let $H_1$ and $H_2$ be stateful oracle handlers that are identical until bad, and let $A$ be any oracle program with private randomness, run from a good initial state $\sigma_0$. Then for every output $x$ and every good final state $\sigma$,

$$\Pr[A^{H_1}(\sigma_0) = (x, \sigma)] = \Pr[A^{H_2}(\sigma_0) = (x, \sigma)].$$

Consequently, for every event $E$ on outputs, $\left|\Pr[A^{H_1} \in E] - \Pr[A^{H_2} \in E]\right| \le \Pr[A^{H_1} \text{ ends in a bad state}]$, and the two bad-event probabilities coincide.

## Proof sketch

Induct on the structure of the program: a step that stays in good states has identical transition probabilities under both handlers, and once a bad state is reached it is never left, so every run ending in a good state passed only through good states. The inequality then follows from Shoup's difference lemma applied to the events "$E$ and final state good".

## Depends on

- [Stateful oracle handlers that are identical until bad](identical-until-bad-handlers.md)

## Proof depends on

- [The difference lemma](../games-and-advantages/advantage-le-win-prob-of-eq-of-not-bad.md)

## Sources

- M. Bellare and P. Rogaway, "The Security of Triple Encryption and a Framework for Code-Based Game-Playing Proofs", Advances in Cryptology (EUROCRYPT 2006), LNCS 4004, 2006.
- V. Shoup, "Sequences of Games: A Tool for Taming Complexity in Security Proofs", IACR Cryptology ePrint Archive, Report 2004/332, 2004.
- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
