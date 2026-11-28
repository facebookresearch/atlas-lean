# Competitive-inhibition mechanism

The competitive-inhibition mechanism is the reaction network $E + S \rightleftharpoons ES \to E + P$, $E + I \rightleftharpoons EI$, in which substrate and inhibitor bind only the free enzyme and never together, with mass-action kinetics. Its substrate and inhibitor variables are free concentrations.

Take the six species $S, I, E, ES, EI, P$ (substrate, inhibitor, free enzyme, enzyme–substrate
complex, dead-end enzyme–inhibitor complex, product), with concentrations $s, i, e, c, y, p$, and the
[chemical reaction network](../../../../Dynamics/smooth-dynamics/reaction-network.md) with the five
reactions

$$E + S \xrightarrow{k_1} ES, \qquad ES \xrightarrow{k_{-1}} E + S, \qquad ES \xrightarrow{k_2} E + P, \qquad E + I \xrightarrow{k_3} EI, \qquad EI \xrightarrow{k_{-3}} E + I,$$

with real rate constants. In the model $k_1, k_2, k_3, k_{-3} > 0$ and $k_{-1} \ge 0$. Its
[mass-action vector field](../../../../Dynamics/smooth-dynamics/mass-action-field.md) gives the system

$$s' = -k_1 e s + k_{-1} c, \qquad i' = -k_3 e i + k_{-3} y, \qquad p' = k_2 c,$$

$$c' = k_1 e s - (k_{-1} + k_2)\, c, \qquad y' = k_3 e i - k_{-3}\, y, \qquad e' = -c' - y'.$$

Functions $s, i, e, c, y, p : \mathbb{R} \to \mathbb{R}$ solve the mechanism on $[0, \infty)$ when
they are differentiable at every $t \ge 0$ with these derivatives. The constants of the mechanism are
the [Michaelis constant](../michaelis-constant.md) $K_M = (k_{-1} + k_2)/k_1$, the substrate
dissociation constant $K_S = k_{-1}/k_1$ and the enzyme–inhibitor dissociation constant
$K_I = k_{-3}/k_3$. Here $i$ is the free inhibitor; the total inhibitor is $i + y$. Deleting $I$
and $EI$ gives back the [Michaelis–Menten system](../is-solution.md) with $k_b = k_{-1}$.

## Depends on

- [Chemical reaction network](../../../../Dynamics/smooth-dynamics/reaction-network.md)
- [Mass-action vector field](../../../../Dynamics/smooth-dynamics/mass-action-field.md)
- [Michaelis constant](../michaelis-constant.md)

## Proof depends on

None.

## Expansion

The order of species is $(S, I, E, ES, EI, P)$. Reaction $E + S \to ES$ has source complex
$S + E$ and product complex $ES$, so it contributes $k_1 e s\,(-1, 0, -1, 1, 0, 0)$ to the field;
the other four reactions are read in the same way. A mechanism specifies elementary steps; it is a
modelling hypothesis about an enzyme, not something a steady-state rate law can certify.

## Sources

- J. Eilertsen, S. Schnell and S. Walcher, "Natural parameter conditions for singular perturbations of
  chemical and biochemical reaction networks", *Bulletin of Mathematical Biology* 85 (2023), article 48, <https://doi.org/10.1007/s11538-023-01150-7>; locators from the version read, arXiv:2211.10836v2 (2023), Section 6.3, Eqs. (74) and
  (75) (the irreversible competitive inhibition mechanism, its mass-action system with conservation
  laws, and the standard initial data $s(0) = s_0$, $e(0) = e_0$, $i(0) = i_0$,
  $c_1(0) = c_2(0) = p(0) = 0$), <https://arxiv.org/abs/2211.10836v2>.
