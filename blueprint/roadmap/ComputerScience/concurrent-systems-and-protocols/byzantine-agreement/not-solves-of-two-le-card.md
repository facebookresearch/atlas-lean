# No synchronous protocol reaches Byzantine agreement when $2 \le n \le 3m$

Let there be at least two values and finitely many processes, $n$ of them, with $2 \le n \le 3m$. Then no deterministic synchronous protocol reaches Byzantine agreement with at most $m$ faulty processes, in any number of rounds. With a single process the statement fails: deciding one's own input tolerates one fault.

The model is the one of [Synchronous Byzantine agreement protocol](agreement-protocol.md): synchronous rounds, Byzantine failures, a complete network of reliable links with known senders, no signatures.

## Informally uses

- [No synchronous protocol reaches Byzantine agreement when $3 \le n \le 3m$](not-solves-of-card-le-three-mul.md): the bound of Fischer, Lynch and Merritt for $n \ge 3$.
- [No synchronous protocol for two processes reaches Byzantine agreement with one fault](not-solves-of-card-eq-two.md): the case $n = 2$.
