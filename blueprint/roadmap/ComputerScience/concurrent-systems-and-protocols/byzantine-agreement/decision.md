# Decision of a process in Byzantine agreement

Let $Q$ be a [synchronous Byzantine agreement protocol](agreement-protocol.md), $x : G \to V$ an assignment of inputs, $F$ a finite set of faulty processes, $\mathit{adv}$ a behaviour of the faulty processes and $T \in \mathbb{N}$. The decision of process $i$ after $T$ rounds is $\mathrm{decide}(i, s)$, where $s$ is the [state](state.md) of $i$ after $T$ rounds of $Q$ with inputs $x$, faulty processes $F$ and behaviour $\mathit{adv}$.
