# Running an oracle algorithm on a randomness tape

Fix a deterministic algorithm $e : M \times \mathrm{Rnd} \to C$ (typically encryption with explicit randomness), a default value $d$ and a continuation $K$ that maps an output $a$, a length $n'$ and a tape $\rho' \in \mathrm{Rnd}^{n'}$ to a value. For an oracle algorithm $c$ with queries in $M$ and answers in $C$, a length $n$ and a tape $\rho = (\rho_0, \dots, \rho_{n-1}) \in \mathrm{Rnd}^n$, the run of $c$ on $\rho$ is defined by recursion on $c$:

- if $c$ returns $a$, the value is $K(a, n, \rho)$, for every $n$ including $n = 0$;
- if $c$ asks a query and the tape is empty ($n = 0$), the value is $d$;
- if $c$ asks the query $m$ and $n = n' + 1$, the query is answered by $e(m, \rho_0)$ and the run continues on the tail $(\rho_1, \dots, \rho_{n'})$.

So the run has two exits. A computation that returns just after consuming the last entry succeeds, and so does a computation that returns at once on the empty tape; only a **further query** with no entry left gives the default $d$. Passing the unused tape to $K$ is what two-phase experiments need.
