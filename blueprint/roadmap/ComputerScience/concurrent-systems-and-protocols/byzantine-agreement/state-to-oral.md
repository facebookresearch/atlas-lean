# The commander protocol simulates the agreement protocol

Let $Q$ be a [synchronous Byzantine agreement protocol](agreement-protocol.md), $c$ a commander, $d$ a default order, $m_0$ a default message, $v$ an order, $F$ a finite set of traitors and $\mathit{adv}$ a behaviour of the traitors in the [commander protocol built from $Q$](to-oral.md). For every round $r$ and every loyal general $i \notin F$, the state of $i$ after round $r + 1$ of the commander protocol (with commander $c$, order $v$, traitors $F$ and behaviour $\mathit{adv}$) is its [state](state.md) after round $r$ of $Q$ with:

- as input of each general $j$, the [order carried](order-of.md) (with default $d$) by the message $j$ received from $c$ in round $0$;
- the same faulty processes $F$;
- as message of a faulty process $j$ to $i$ in round $r'$, the [protocol message carried](msg-of.md) (with default $m_0$) by the message $\mathit{adv}(r' + 1, j, i)$.
