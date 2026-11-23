# Oral-message protocol

A synchronous oral-message protocol for a set $G$ of generals, with
orders in $V$, local states in $\sigma$ and messages in $M$, consists of an initial state for
each general in $G$, used by the generals other than the commander; an initial state of the
commander for each order in $V$; a sending function giving, for each round $r$, each general $j$
in each state $s$ and each general $i$, the message in $M$ that $j$ sends to $i$ in round $r$; a
transition function giving, for each round $r$, each general $i$ in each state $s$ and each
assignment of a message to every sender $j$, the state of $i$ after round $r$; and a decision
function giving the value in $V$ that each general decides in each state.

The commander is not part of the protocol: it is chosen when the protocol is run. In each round
every general sends its messages from its current state and then moves to the state given by the
transition function on the messages it received. Only the commander's initial state depends on
the order.
