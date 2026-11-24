# Executions of an oral-message protocol

Let $P$ be an oral-message protocol for the
generals $G$, let $c \in G$ be the commander, $v$ its order and $S \subseteq G$ a finite set of
traitors, and let $a_r(j, i)$ be the message a traitor $j$ sends general $i$ in round $r$. The
state of general $i$ after $r$ rounds is defined by recursion on $r$. After $0$ rounds it is
the initial state of $i$ for commander $c$ and order $v$. After $r + 1$ rounds it is the state
to which $i$ moves by its code for round $r$ from its state after $r$ rounds, on receiving
$a_r(j, i)$ from each traitor $j \in S$ and, from each other general $j$, the message that $P$
has $j$ send to $i$ in round $r$ from the state of $j$ after $r$ rounds.
