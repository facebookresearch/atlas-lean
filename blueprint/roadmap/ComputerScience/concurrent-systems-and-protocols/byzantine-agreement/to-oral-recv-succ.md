# Later rounds of the commander protocol

Let $Q$ be a [synchronous Byzantine agreement protocol](agreement-protocol.md) and consider the [commander protocol built from $Q$](to-oral.md) with commander $c$, default order $d$ and default message $m_0$. In a round $r + 1$, a general $i$ in a state $t$ of $Q$ that receives the messages $\mathit{msg}(j)$ moves to the state $\mathrm{recv}(r, i, t, \mathit{msg}')$ of $Q$, where $\mathit{msg}'(j)$ is the [protocol message carried](msg-of.md) by $\mathit{msg}(j)$ (default $m_0$): it runs round $r$ of $Q$.
