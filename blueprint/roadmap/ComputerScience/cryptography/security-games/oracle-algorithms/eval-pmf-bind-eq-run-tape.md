# Eager sampling with a continuation

Let $\mathrm{Rnd}$ be finite and nonempty and $e : M \times \mathrm{Rnd} \to C$. Let $D$ be any distribution on $\beta$ (the default), $\mathsf{cont}$ a predicate on outputs and natural numbers, $K$ a map from outputs to distributions on $\beta$, and $K'$ a map from an output $a$, a length $n$ and a tape in $\mathrm{Rnd}^n$ to distributions on $\beta$, such that whenever $\mathsf{cont}(a, n)$ holds, drawing a uniform tape $\rho' \in \mathrm{Rnd}^n$ and then sampling $K'(a, n, \rho')$ has distribution $K(a)$.

Let $c$ be an oracle algorithm (queries in $M$, answers in $C$) that makes at most $q$ queries along every path and whose every output $a$, reached with $n$ queries of budget unused, satisfies $\mathsf{cont}(a, n)$. Then running $c$ against the randomized oracle $m \mapsto e(m, r)$ with a fresh uniform $r$ per query and then sampling $K$ on the output has the same distribution as drawing a uniform tape $\rho \in \mathrm{Rnd}^q$ up front and taking the [tape run](run-tape.md) of $c$ on $\rho$ with default $D$ and continuation $K'$.

On the tape side, $K'(a, n, \cdot)$ receives only the $n$ unused entries of the tape, not the original tape. Under the query bound the default is never reached.
