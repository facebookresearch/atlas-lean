# Diode branch

Consider a network with finitely many nodes and branches, tail and head maps on branches, and electrical incidence $A_{u e} = [\mathrm{tail}(e) = u] - [\mathrm{head}(e) = u]$. Given parameters $I_s, n, k_B, T, q$, nodes $a, c$, a branch $e$ and branch voltages $v$ and currents $i$, the diode branch predicate says that a diode with anode $a$ and cathode $c$ occupies branch $e$:

- either $\mathrm{tail}(e) = a$ and $\mathrm{head}(e) = c$, or $\mathrm{tail}(e) = c$ and $\mathrm{head}(e) = a$; and
- $i_e = s\, I_D(s\, v_e)$, where $s = A_{a e}$ and $I_D(V) = I_s\left(e^{V/(n V_T)} - 1\right)$ with $V_T = k_B T/|q|$.

When $a \neq c$, $s = +1$ if the anode is the branch tail and $s = -1$ if it is the head. The parameters are unrestricted: if $n V_T = 0$ (for instance $n = 0$, $T = 0$ or $q = 0$, where $V_T = 0$ by the convention $x/0 = 0$), the same convention makes $I_D$ identically $0$.
