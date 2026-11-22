# Decision under crash failures

Let $Q$ be a [synchronous protocol with crash failures](crash-protocol.md), $x : G \to V$ an assignment of inputs, $\pi$ a [crash pattern](crash-pattern.md) and $T \in \mathbb{N}$. The decision of process $i$ after $T$ rounds is $\mathrm{decide}(i, s)$, where $s$ is the [state](state.md) of $i$ after $T$ rounds of $Q$ with inputs $x$ and crash pattern $\pi$. It is defined for every process; for a process that has crashed it is a formal value, and the consensus conditions constrain only the decisions of correct processes.
