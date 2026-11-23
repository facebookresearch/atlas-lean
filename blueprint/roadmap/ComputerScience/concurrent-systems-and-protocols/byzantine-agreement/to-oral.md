# Byzantine generals from Byzantine agreement

Let $Q$ be a [synchronous Byzantine agreement protocol](agreement-protocol.md) for processes $G$, inputs $V$, states $\sigma$ and messages $M$, and let $c \in G$, $d \in V$ and $m_0 \in M$. The commander protocol built from $Q$ is the [oral-message protocol](../byzantine-generals-problem/oral-protocol.md) with commander $c$ whose states are either an optional order or a state of $Q$, and whose messages are either an optional order or a message of $Q$:

- a general starts with no order, and the commander with order $v$ starts holding $v$;
- in round $0$ each general sends the optional order it holds (so the commander sends its order to everyone and the others send no order), and each general $i$ then moves to the state $\mathrm{init}(i, v_i)$ of $Q$, where $v_i$ is the [order carried](order-of.md) by the message it received from $c$ ($d$ if the message carries no order);
- in a round $r + 1$, a general in a state of $Q$ runs round $r$ of $Q$: it sends the messages of $Q$ and moves as $Q$ does, reading each received message through the [protocol message it carries](msg-of.md) (default $m_0$); a general still holding an optional order sends no order and keeps its state;
- a general in a state $t$ of $Q$ decides $\mathrm{decide}(i, t)$, and a general holding an optional order decides $d$.

Messages of the wrong kind, which only traitors send, are read as $d$ or $m_0$.
