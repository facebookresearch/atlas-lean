# Ideal diode as a network branch port

Let $V_T = k_B T/|q|$ be the thermal voltage and $I_D(V) = I_s\left(e^{V/(n V_T)} - 1\right)$ the Shockley diode current at anode-to-cathode voltage $V$, with saturation current $I_s$ and emission coefficient $n$. Consider a network with finitely many nodes and branches, branch tail and head maps, and electrical incidence matrix $A$ with entries $A_{u e} = [\mathrm{tail}(e) = u] - [\mathrm{head}(e) = u]$. Let $a \neq c$ be nodes, $\phi$ node potentials, and $v, i$ branch voltages and currents with $v = A^{\mathsf T}\phi$. Suppose a diode with anode $a$ and cathode $c$ occupies branch $e$: the branch joins $a$ and $c$ in one of the two orientations and $i_e = s\, I_D(s\, v_e)$, where $s = A_{a e}$.

Assume $I_s > 0$, $n > 0$, $k_B > 0$, $T > 0$ and $q \neq 0$. Then:

1. $V_T > 0$, and $V_T$ is unchanged when $q$ is replaced by $-q$;
2. $I_D(0) = 0$;
3. for every $x$, $I_D$ has derivative $\dfrac{I_s}{n V_T}\, e^{x/(n V_T)}$ at $x$;
4. $I_D$ is strictly increasing;
5. for every $x$, $I_D(x) > 0 \iff x > 0$;
6. for every $x$, $-I_s < I_D(x)$;
7. $I_D(x) \to -I_s$ as $x \to -\infty$;
8. $s\, i_e = I_D(\phi_a - \phi_c)$;
9. reversing branch $e$ (swapping its tail and head) and negating $v_e$ and $i_e$ again gives a diode with anode $a$ and cathode $c$ on branch $e$.
