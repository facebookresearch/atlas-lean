# Setup constraint for a register-to-register path through a circuit

Let $c$ be a circuit, a straight-line program of gates over a signature with designated output
wires, let $d_j \in \mathbb{R}$ be the delay of gate $j$ and $a_i \in \mathbb{R}$ the arrival time
of input $i$. Arrival times follow the gate-delay model: input $i$ arrives at $a_i$, and a gate $j$
that reads the wires $w_1, \dots, w_k$ arrives at

$$d_j + \max\bigl(0, A(w_1), \dots, A(w_k)\bigr),$$

its delay plus the latest arrival among the wires it reads, the maximum being taken from the time
origin $0$; so a constant gate, which reads no wire, arrives at $d_j$. A designated output $o$
arrives at the time $A_o$ of the wire that carries it. For reals $t_s$, $u$ and $T$, the setup
constraint holds when

$$A_o + t_s + u \le T \qquad \text{for every designated output } o.$$

It holds trivially for a circuit without designated outputs.

In the timing reading, a clock edge at time $0$ launches the path and the next edge, at the clock
period $T$, captures it; the circuit inputs are the launching register's outputs, $t_s$ is the
capturing register's setup time and $u$ the clock uncertainty, all times in seconds. The constraint
says that every output settles at least $t_s + u$ before the capturing edge. Physically the delays,
$t_s$ and $u$ are nonnegative and $T > 0$; the definition accepts any reals.
