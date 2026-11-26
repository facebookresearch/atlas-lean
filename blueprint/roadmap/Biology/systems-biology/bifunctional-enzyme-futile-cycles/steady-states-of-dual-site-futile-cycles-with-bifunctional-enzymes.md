# Steady states of dual-site futile cycles with bifunctional enzymes

**Model.** A substrate is phosphorylated in two steps by a kinase $E$ and dephosphorylated by bifunctional compounds $\mathcal E_1, \mathcal E_2 \in \{C_1, C_2\}$:

$$S_0 + E \rightleftarrows C_1 \to S_1 + E, \qquad S_1 + E \rightleftarrows C_2 \to S_2 + E,$$

$$S_1 + \mathcal E_1 \rightleftarrows C_4 \to S_0 + \mathcal E_1, \qquad S_2 + \mathcal E_2 \rightleftarrows C_3 \to S_1 + \mathcal E_2,$$

under mass action, with conserved totals $T_e$ (enzyme) and $T_s$ (substrate). The four networks are denoted $(E,E,\mathcal E_2,\mathcal E_1)$. Write $k_i^*$ for the effective constants built from the rate constants of step $i$ (an absolute concentration robustness, ACR, value has the form $k_i/k_j^*$).

**Theorem.**
1. *(ACR.)* $(E,E,C_2,C_1)$ has ACR in $S_1$ and $S_2$ (values $k_1/k_4^*$, $k_2/k_3^*$); $(E,E,C_1,C_1)$ has ACR in $S_1$; $(E,E,C_2,C_2)$ has ACR in $S_2$; $(E,E,C_1,C_2)$ has ACR in no species.
2. *$(E,E,C_2,C_1)$:* a unique "dead" boundary steady state ($e = T_e$, $s_2 = T_s$), stable iff $T_s < k_2/k_3^*$; for $T_s > k_2/k_3^*$ a unique "living" boundary steady state (the $S_1 \rightleftarrows S_2$ subcycle on, $S_0$ absent), stable iff $T_s < T_s^{2,1}$ for an explicit threshold $T_s^{2,1}$; exactly one positive steady state for $T_s > T_s^{2,1}$, and at most two positive steady states in general (two can occur).
3. *$(E,E,C_1,C_1)$:* the boundary steady state is always locally stable; positive steady states exist for $T_s > T_s^{1,1}$, come in even number (with multiplicity), and number at most two.
4. *$(E,E,C_1,C_2)$:* the boundary steady state is always locally stable; positive steady states exist above a threshold, are even in number, at most four (four can occur), and two stable positive steady states can coexist.
5. *$(E,E,C_2,C_2)$:* the boundary steady state is stable for $T_s < k_2/k_3^*$ and unstable above; positive steady states exist iff $T_s > k_2/k_3^*$, are odd in number, at most three (three can occur), and two stable positive steady states can coexist.

## Expansion

When the reverse catalyst is a kinase–substrate compound, every reverse flux is proportional to a forward intermediate, and at steady state this forces the Shinar–Feinberg ACR relation on the modified form that the compound dephosphorylates. Positive steady states correspond one-to-one to positive roots of a polynomial in a single ratio $u$, whose degree and sign pattern give the parity and capacity counts. Stability of boundary steady states, where linearisation is degenerate, is decided by a next-generation-matrix criterion $\rho(F V^{-1}) \lessgtr 1$ on the face. Varying $T_s$ then produces saddle-node and transcritical bifurcations, hysteresis in the bistable networks, and in $(E,E,C_1,C_2)$ an invariant product of two intermediates that can make the final product decrease with total substrate.

## Sources

- B. Joshi, T. D. Nguyen, M. D. Johnston, "Bistability, Absolute Concentration Robustness, and Hysteresis in Dual-Site Futile Cycles with Bifunctional Enzymes", arXiv:2605.11389 (2026), Theorems 2.3, 4.1, 4.4, 4.5, 4.7, 4.9 and 4.12, <https://doi.org/10.48550/arXiv.2605.11389>.
