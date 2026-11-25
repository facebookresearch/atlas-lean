# Setup timing constraint

Let $c$ be a combinational circuit with gate delays $\delta_j$ and input arrival times $a^{\mathrm{in}}_i$, and let $a_o$ be the arrival time of output $o$ computed by the gate-delay model of $c$ from these delays and input arrivals. For a setup time $t_s$, a clock uncertainty $u$ and a clock period $T$, the setup constraint holds when

$$a_o + t_s + u \le T \quad \text{for every output } o.$$

This models one register-to-register path launched by a clock edge at time $0$ and captured by the next edge at time $T$.
