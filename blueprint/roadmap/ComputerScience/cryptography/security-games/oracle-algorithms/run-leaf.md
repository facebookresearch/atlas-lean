# Where a tape run stops

For a deterministic algorithm $e : M \times \mathrm{Rnd} \to C$, an oracle algorithm $c$ (queries in $M$, answers in $C$), a length $n$ and a tape $\rho \in \mathrm{Rnd}^n$, the stopping point of the run of $c$ on $\rho$ is an optional pair: it is the [tape run](run-tape.md) with default "none" and continuation $(a, n', \rho') \mapsto (a, (n', \rho'))$. Hence

- it is "none" exactly when the run reaches a query with no tape entry left;
- otherwise it is the output $a$ together with the unused suffix $\rho'$ of the tape and its length $n'$.

A computation that returns right after consuming the last entry, or at once on the empty tape, stops with $n' = 0$; it does not give "none".
