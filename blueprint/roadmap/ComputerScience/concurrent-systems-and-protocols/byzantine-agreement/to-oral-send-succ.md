# Later messages of the commander protocol

Let $Q$ be a [synchronous Byzantine agreement protocol](agreement-protocol.md) and consider the [commander protocol built from $Q$](to-oral.md) with commander $c$, default order $d$ and default message $m_0$. In a round $r + 1$, a general $j$ in a state $t$ of $Q$ sends to each general $i$ the message $\mathrm{send}(r, j, t, i)$ of round $r$ of $Q$.
