# For nonzero total impedance, every phase of the fault solves the laws

Let $E$, $Z_{\mathrm{th}}$ and $Z_f$ be complex with $Z_{\mathrm{th}} + Z_f \neq 0$, and let $I_f$
and $V_f$ be the [fault current](fault-current.md) and the [fault voltage](fault-voltage.md). For
each phase, indexed by $p = 0, 1, 2$ in the integers modulo 3 (phases $a$, $b$, $c$), let $E_p$,
$V_{f,p}$ and $I_{f,p}$ be the $p$-th entries of $(E, \alpha^2 E, \alpha E)$,
$(V_f, \alpha^2 V_f, \alpha V_f)$ and of the [fault phase currents](fault-phase-currents.md)
$(I_f, \alpha^2 I_f, \alpha I_f)$, where $\alpha = e^{2\pi i/3}$ is the
[rotation operator](../symmetrical-components-of-three-phase-systems/alpha.md). Then the
[Thévenin fault laws](is-thevenin-fault.md) hold in every phase:
$V_{f,p} = E_p - Z_{\mathrm{th}}\, I_{f,p}$ and $V_{f,p} = Z_f\, I_{f,p}$.
