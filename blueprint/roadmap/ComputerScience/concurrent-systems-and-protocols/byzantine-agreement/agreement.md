# Agreement condition of Byzantine agreement

Let $Q$ be a [synchronous Byzantine agreement protocol](agreement-protocol.md), $x : G \to V$ an assignment of inputs, $F \subseteq G$ a finite set of faulty processes, $\mathit{adv}$ a behaviour of the faulty processes and $T \in \mathbb{N}$. The agreement condition holds when, after $T$ rounds, any two processes $i, j \notin F$ [decide](decision.md) the same value.
