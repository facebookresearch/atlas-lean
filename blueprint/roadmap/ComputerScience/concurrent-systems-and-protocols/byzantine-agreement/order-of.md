# Order carried by a first-round message

Let $V$ be a set of orders, $M$ the set of messages of a Byzantine agreement protocol and $d \in V$. A message of the [commander protocol built from it](to-oral.md) is either an optional order or a message of $M$; the order it carries is $v$ if it is the order $v \in V$, and $d$ otherwise (no order, or a message of $M$).
