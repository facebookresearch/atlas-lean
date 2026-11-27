# Protocol message carried by a later message

Let $V$ be a set of orders, $M$ the set of messages of a Byzantine agreement protocol and $m_0 \in M$. A message of the [commander protocol built from it](to-oral.md) is either an optional order or a message of $M$; the protocol message it carries is $m$ if it is a message $m \in M$, and $m_0$ otherwise.
