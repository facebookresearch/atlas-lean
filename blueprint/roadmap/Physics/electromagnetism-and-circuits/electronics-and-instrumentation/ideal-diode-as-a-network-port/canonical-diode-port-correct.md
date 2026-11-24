# Properties of the ideal diode law and of a diode branch

Let $I_s > 0$, $n > 0$, $k_B > 0$, $T > 0$ and $q \ne 0$. Let a network with finite sets of nodes
and branches carry branch voltages $v$ obtained from node potentials $\phi$ through the transposed
[electrical incidence](../../circuit-theory/tellegen-s-theorem-and-branch-power-balance/electrical-incidence.md), and
let a [diode occupy branch](diode-branch.md) $e$ with anode $a$ and cathode $c$, $a \ne c$. With
the [thermal voltage](thermal-voltage.md) $V_T = k_B T / |q|$ and the
[diode current](diode-current.md) $I_D$:

- $V_T > 0$, and $V_T$ is the same for the charges $q$ and $-q$;
- $I_D(0) = 0$;
- for every $x$, $I_D$ has derivative $\frac{I_s}{n V_T} \exp\frac{x}{n V_T}$ at $x$;
- $I_D$ is strictly increasing;
- for every $x$, $I_D(x) > 0$ if and only if $x > 0$;
- for every $x$, $I_D(x) > -I_s$, and $I_D(x) \to -I_s$ as $x \to -\infty$;
- the anode-to-cathode current is $s\, i_e = I_D(\phi(a) - \phi(c))$, where $s = \pm 1$ is the
  orientation sign of the anode on branch $e$;
- reversing branch $e$ together with $v_e$ and $i_e$ keeps the same diode on that branch.
