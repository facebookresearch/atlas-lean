# Accumulated bad-event probability over a query-bounded run

Let $H$ be a stateful oracle handler and $\mathrm{Bad}$ an absorbing set of states. Suppose that from every good state each query leads to a bad state with probability at most $\delta$. Then for every oracle program $A$ that makes at most $q$ queries on every execution path,

$$\Pr[A^{H}(\sigma_0) \text{ ends in a bad state}] \le q\,\delta$$

for every good initial state $\sigma_0$. More generally, if the per-query bound from a state $\sigma$ is $\delta(\sigma)$ and each query increases a size measure by at most one, the bound is the sum of the per-step bounds along the worst path.

## Proof sketch

Induct on the query budget: the first query triggers bad with probability at most $\delta$, and conditioned on staying good the residual program has budget $q-1$. Union bounding over the steps gives the claim.

## Depends on

- [Stateful oracle handlers that are identical until bad](identical-until-bad-handlers.md)
- [Query bound](../oracle-algorithms/is-query-bounded.md)

## Sources

- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
- M. Bellare and P. Rogaway, "The Security of Triple Encryption and a Framework for Code-Based Game-Playing Proofs", Advances in Cryptology (EUROCRYPT 2006), LNCS 4004, 2006.
