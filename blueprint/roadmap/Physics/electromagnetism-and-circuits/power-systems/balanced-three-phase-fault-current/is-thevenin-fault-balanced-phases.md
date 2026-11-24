# A one-phase solution of the fault laws gives a solution in every phase

Let $E$, $Z_{\mathrm{th}}$, $Z_f$, $V$ and $I$ be complex numbers that satisfy the
[Thévenin fault laws](is-thevenin-fault.md) $V = E - Z_{\mathrm{th}}\, I$ and $V = Z_f\, I$. For
each phase, indexed by $p = 0, 1, 2$ in the integers modulo 3 (phases $a$, $b$, $c$), let $E_p$,
$V_p$ and $I_p$ be the $p$-th entries of the
[balanced positive-sequence sets](../balanced-three-phase-power/balanced-phases.md)
$(E, \alpha^2 E, \alpha E)$, $(V, \alpha^2 V, \alpha V)$ and $(I, \alpha^2 I, \alpha I)$, where
$\alpha = e^{2\pi i/3}$ is the
[rotation operator](../symmetrical-components-of-three-phase-systems/alpha.md). Then the same laws
hold in every phase with the same impedances: $V_p = E_p - Z_{\mathrm{th}}\, I_p$ and
$V_p = Z_f\, I_p$. No condition on the total impedance is needed.
