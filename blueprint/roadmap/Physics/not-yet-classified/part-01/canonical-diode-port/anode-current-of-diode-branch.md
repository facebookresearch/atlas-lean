# Anode current of a diode branch

In a network with finitely many nodes and branches, tail and head maps on branches, and electrical incidence $A_{u e} = [\mathrm{tail}(e) = u] - [\mathrm{head}(e) = u]$, let $a \neq c$ be nodes, $\phi$ node potentials and $v = A^{\mathsf T}\phi$ the branch voltages. If a diode with anode $a$ and cathode $c$ occupies branch $e$ with branch current $i$ (in the sense of the diode branch predicate, with parameters $I_s, n, k_B, T, q$), then

$$A_{a e}\, i_e = I_D(\phi_a - \phi_c),$$

where $I_D(V) = I_s\left(e^{V/(n V_T)} - 1\right)$ and $V_T = k_B T/|q|$. This holds in either orientation of the branch. The parameters are unrestricted: if $n V_T = 0$ (for instance $n = 0$, $T = 0$ or $q = 0$, where $V_T = 0$ by the convention $x/0 = 0$), the same convention makes $I_D$ identically $0$.
