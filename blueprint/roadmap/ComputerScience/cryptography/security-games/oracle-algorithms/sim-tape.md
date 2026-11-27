# Simulating a tape run by an oracle algorithm

Let $\mathrm{encQ}(m, r)$ be an oracle algorithm querying a keyed function (queries in $Q$, answers in $A$, for example a PRF or a block cipher) that returns a ciphertext in $C$. Fix a default value $d$ and a continuation $K$ mapping an output $a$, a length $n'$ and a tape $\rho' \in \mathrm{Rnd}^{n'}$ to an oracle algorithm over $Q$ and $A$. For an oracle algorithm $c$ with queries in $M$ and answers in $C$, a length $n$ and a tape $\rho \in \mathrm{Rnd}^n$, the simulation is the oracle algorithm over $Q$ and $A$ defined by:

- if $c$ returns $a$, it is $K(a, n, \rho)$;
- if $c$ asks a query and the tape is empty, it returns $d$ at once;
- if $c$ asks $m$ and $n = n' + 1$, it runs $\mathrm{encQ}(m, \rho_0)$ and, with the returned ciphertext as the answer, continues the simulation on the tail of the tape.

It is the oracle-algorithm form of the [tape run](run-tape.md).
