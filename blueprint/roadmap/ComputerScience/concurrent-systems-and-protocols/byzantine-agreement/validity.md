# Validity condition of Byzantine agreement

Let $Q$ be a [synchronous Byzantine agreement protocol](agreement-protocol.md), $x : G \to V$ an assignment of inputs, $F$ a finite set of faulty processes, $\mathit{adv}$ a behaviour of the faulty processes and $T \in \mathbb{N}$. The validity condition holds when, for every value $v$: if $x_i = v$ for every process $i \notin F$, then every process $i \notin F$ [decides](decision.md) $v$ after $T$ rounds.

This is the validity condition of Fischer, Lynch and Merritt (1986, §3). Without it the problem is trivial (always decide a fixed value).

## Sources

- M. J. Fischer, N. A. Lynch, M. Merritt, *Easy impossibility proofs for distributed consensus problems*, Distributed Computing 1(1), 1986, 26–39: §3.
