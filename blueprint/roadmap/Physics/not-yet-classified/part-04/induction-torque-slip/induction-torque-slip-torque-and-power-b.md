# Induction machine torque–slip curve and power balance

Consider the steady-state Thevenin equivalent of an induction machine with Thevenin voltage $V_{th} \in \mathbb{C}$, Thevenin resistance $R_{th}$, rotor resistance $R_2$, equivalent reactance $X_{eq}$, synchronous mechanical speed $\omega_s$ and slip $s$. The rotor current is $I_2(s) = \dfrac{V_{th}\, s}{R_{th} s + R_2 + i X_{eq} s}$, the air-gap power of a rotor current $I$ is $P_{ag} = 3\|I\|^2 R_2/s$, the developed torque is $\tau = P_{ag}/\omega_s$, the rotor copper loss is $P_{cu} = 3\|I\|^2 R_2$, and the converted power is $P_{conv} = P_{ag} - P_{cu}$.

Assume $R_2 > 0$, $\omega_s > 0$, $R_{th} \ge 0$ and $0 < s \le 1$. Let

$$\tau_c(t) = \frac{3\|V_{th}\|^2 R_2\, t}{\omega_s\left((R_{th} t + R_2)^2 + (X_{eq} t)^2\right)}$$

be the rational torque curve. Then, for the rotor current $I_2(s)$:

1. $\tau = \tau_c(s)$;
2. $\tau_c(0) = 0$ and $\tau_c$ is continuous at $t = 0$;
3. $P_{conv} = (1 - s)\, P_{ag}$;
4. $P_{conv} = \tau \cdot (1 - s)\,\omega_s$;
5. $P_{cu} = s\, P_{ag}$.
