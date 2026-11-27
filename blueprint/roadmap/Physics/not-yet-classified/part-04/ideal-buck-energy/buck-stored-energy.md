# Stored energy of the buck converter

For inductance $L$, capacitance $C$, inductor current $i$ and capacitor voltage $v$, the stored energy at time $t$ is the network stored energy $\sum_{e \in \mathcal{C}} C_e v_e^2/2 + \sum_{e \in \mathcal{L}} L_e i_e^2/2$ on four branches ordered source, inductor, capacitor, resistor, with capacitor set $\mathcal{C} = \{2\}$, $C_2 = C$, $v_2 = v(t)$, and inductor set $\mathcal{L} = \{1\}$, $L_1 = L$, $i_1 = i(t)$; all other entries are zero. Thus

$$E(t) = \frac{C\, v(t)^2}{2} + \frac{L\, i(t)^2}{2}.$$
