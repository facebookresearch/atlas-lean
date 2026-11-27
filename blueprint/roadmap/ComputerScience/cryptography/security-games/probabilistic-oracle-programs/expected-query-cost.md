# Expected query cost of a probabilistic oracle program

For a probabilistic oracle program $A$ run against a handler $h$ from state $\sigma_0$, and a cost function $c : Q \to \mathbb{N}$ on queries, the *expected query cost* is

$$\mathbb{E}\Bigl[\sum_{\text{queries } q \text{ asked in the run}} c(q)\Bigr],$$

the expectation being over the private coins and the handler's randomness. It is bounded above by the worst-case budget $\max_{\text{paths}} \sum c(q)$, and for a program with worst-case query bound $B$ under unit cost it is at most $B$. Expected cost is additive under sequential composition and is preserved by handlers that agree on all queries the program can make.

## Depends on

- [Probabilistic oracle program and its semantics against a stateful handler](probabilistic-oracle-program.md)
- [Query bound](../oracle-algorithms/is-query-bounded.md)

## Sources

- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
