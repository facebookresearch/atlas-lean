# Consensus against $T$ crashes, at most one per round, needs more than $T$ rounds

If there are finitely many processes, at least $T + 2$ of them, and at least two values, no deterministic synchronous protocol solves consensus in $T$ rounds against the crash patterns whose crashes happen before round $T$, at most one per round. This is Theorem 1 of Aguilera and Toueg (1999) with $t = T$: "Consider a synchronous round-based system S with n processes and at most t crash failures such that at most one process crashes in each round. If n > t + 1 then there is no algorithm that solves consensus in t rounds in S."

**Relation to the source.** Aguilera and Toueg's system also allows crashes in rounds $T$ and later, which change nothing before the decisions; the hypothesis here quantifies only over crashes before round $T$, so it is weaker than theirs and the theorem is at least as strong as their Theorem 1. With a single process the hypothesis on $n$ fails and consensus is solvable (the process decides its own input).

**Model.** Synchronous rounds; crash failures as in [Crash pattern](crash-pattern.md); a complete network of reliable links with known senders; deterministic protocols deciding at the end of round $T$.

**Proof.** The bivalency proof of Aguilera and Toueg. If $T = 0$ the argument is that of [Consensus needs a round](not-solves-zero.md). Otherwise: every partial run up to round $T - 1$ is univalent (their Lemma 2); some initial configuration is bivalent (their Lemma 3, the chain argument of Fischer, Lynch and Paterson with a process crashed at the start); and a bivalent partial run up to a round $k < T - 1$ has a bivalent one-round extension (their Lemma 4, crashing a process in round $k$ and, to hide who heard it, another one silently in round $k + 1$). Together they give a bivalent partial run up to round $T - 1$, a contradiction.

## Informally uses

- [An admissible pattern has at most $T$ faulty processes](card-faulty-le.md): the patterns used have at most $T$ faults, so at least two correct processes.
- [A silent process changes nothing for the others](state-eq-of-silent.md) and [Executions agree while deliveries agree](state-congr.md): the indistinguishability steps.

## Background

- [A bivalent initial state](../flp-impossibility/exists-bivalent-start.md): Aguilera and Toueg's Lemma 3 is the same chain argument as Lemma 2 of Fischer, Lynch and Paterson ("Same as in Fischer et al.").
- [Solving consensus against at most one crash per round](solves-one-per-round.md): the hypothesis.

## Sources

- M. K. Aguilera, S. Toueg, *A simple bivalency proof that t-resilient consensus requires t + 1 rounds*, Information Processing Letters 71(3–4), 1999, 155–158: Theorem 1, Lemmas 2–4.
