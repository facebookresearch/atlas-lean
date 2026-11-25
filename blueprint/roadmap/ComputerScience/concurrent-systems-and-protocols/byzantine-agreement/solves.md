# Reaching Byzantine agreement

Let $Q$ be a [synchronous Byzantine agreement protocol](agreement-protocol.md) and $m, T \in \mathbb{N}$. The protocol $Q$ reaches Byzantine agreement with at most $m$ faulty processes in $T$ rounds if, for every assignment of inputs $x : G \to V$, every finite set $F$ of at most $m$ faulty processes and every behaviour $\mathit{adv}$ of the faulty processes, the [agreement](agreement.md) and [validity](validity.md) conditions hold after $T$ rounds.
