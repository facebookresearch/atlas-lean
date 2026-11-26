# Planted-query guessing: bounding a bad event by a reduction that guesses its index

Let an oracle latch a bad event at the first query $q$ (among queries of a designated *target* kind) that satisfies a predicate $\mathrm{isBad}(q, \sigma)$, and let the adversary make at most $Q$ target queries. Consider the reduction that guesses an index $j \in \{0, \dots, Q-1\}$ uniformly, answers the first $j$ target queries by a faithful simulation, and outputs the $(j{+}1)$-st target query. Then

$$\Pr[\text{bad event occurs}] \le Q \cdot \Pr[\text{the reduction's output } q \text{ satisfies } \mathrm{isBad}].$$

## Proof sketch

Split the bad event by the index of the first bad target query. Conditioned on the guess $j$ being that index, the reduction's simulation agrees with the real run up to that query, so its output is bad; the guess is correct with probability $1/Q$ independently of the run.

## Depends on

- [Stateful oracle handlers that are identical until bad](identical-until-bad-handlers.md)
- [Query bound](../oracle-algorithms/is-query-bounded.md)

## Proof depends on

- [Fundamental lemma of game playing for stateful oracle handlers](fundamental-lemma-for-stateful-handlers.md)

## Sources

- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
- V. Shoup, "Sequences of Games: A Tool for Taming Complexity in Security Proofs", IACR Cryptology ePrint Archive, Report 2004/332, 2004.
