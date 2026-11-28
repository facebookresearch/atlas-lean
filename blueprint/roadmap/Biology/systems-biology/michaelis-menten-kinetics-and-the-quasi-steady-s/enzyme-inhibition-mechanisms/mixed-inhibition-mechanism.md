# Mixed-inhibition mechanism

The mixed (two-site) inhibition mechanism adds to competitive inhibition a dead-end step $ES + I \rightleftharpoons ESI$: the inhibitor binds both the free enzyme and the enzyme–substrate complex, and neither inhibitor complex makes product. It is one mechanism with mixed kinetics, not the only one.

Take the seven species $S, I, E, ES, EI, ESI, P$ with concentrations $s, i, e, c, y, z, p$, and the
[chemical reaction network](../../../../Dynamics/smooth-dynamics/reaction-network.md) with the seven
reactions

$$E + S \xrightarrow{k_1} ES, \quad ES \xrightarrow{k_{-1}} E + S, \quad ES \xrightarrow{k_2} E + P, \quad E + I \xrightarrow{k_3} EI, \quad EI \xrightarrow{k_{-3}} E + I, \quad ES + I \xrightarrow{k_4} ESI, \quad ESI \xrightarrow{k_{-4}} ES + I,$$

with real rate constants; in the model $k_1, k_2, k_3, k_{-3}, k_4, k_{-4} > 0$ and $k_{-1} \ge 0$.
This page chooses the restricted mechanism with no step $EI + S \rightleftharpoons ESI$ and no product-forming step from $ESI$. These exclusions are modelling assumptions: the inhibitor competes with substrate for free enzyme and binds a separate site on $ES$. The
[mass-action vector field](../../../../Dynamics/smooth-dynamics/mass-action-field.md) gives

$$s' = -k_1 e s + k_{-1} c, \qquad i' = -k_3 e i + k_{-3} y - k_4 c i + k_{-4} z, \qquad p' = k_2 c,$$

$$c' = k_1 e s - (k_{-1} + k_2)\, c - k_4 c i + k_{-4} z, \qquad y' = k_3 e i - k_{-3} y, \qquad z' = k_4 c i - k_{-4} z,$$

and $e' = -c' - y' - z'$. A solution on $[0, \infty)$ is a tuple of real functions differentiable at
every $t \ge 0$ with these derivatives. The constants are the
[Michaelis constant](../michaelis-constant.md) $K_M = (k_{-1} + k_2)/k_1$ and the dissociation
constants $K_{EI} = k_{-3}/k_3$ of $EI$ and $K_{ES.I} = k_{-4}/k_4$ of $ESI$ into $ES + I$.

Special cases: $k_4 = k_{-4} = 0$ with $z \equiv 0$ is the
[competitive mechanism](competitive-inhibition-mechanism.md); $k_3 = k_{-3} = 0$ with $y \equiv 0$
is the uncompetitive mechanism $E + S \rightleftharpoons ES \to E + P$,
$ES + I \rightleftharpoons ESI$.

## Depends on

- [Chemical reaction network](../../../../Dynamics/smooth-dynamics/reaction-network.md)
- [Mass-action vector field](../../../../Dynamics/smooth-dynamics/mass-action-field.md)
- [Michaelis constant](../michaelis-constant.md)

## Proof depends on

None.

## Expansion

The enzyme forms $E, ES, EI, ESI$ are joined by the binding steps $E$–$ES$, $E$–$EI$ and $ES$–$ESI$
(the catalytic step $ES \to E + P$ supplies a parallel route from $ES$ to $E$). Each inhibitor complex is a dead-end leaf attached by one reversible pair, so stationarity forces that pair's net flux to vanish. Adding $EI + S \rightleftharpoons ESI$ would close
a cycle; that mechanism is a different model and is not covered here. Mixed inhibition patterns also
arise from mechanisms in which the inhibitor binds only the active site, for example tight-binding
inhibition analysed with free and total inhibitor confused, or enzymes with a slow isomerization
step.

## Sources

- A. Pesaresi, "Mixed and non-competitive enzyme inhibition: underlying mechanisms and mechanistic
  irrelevance of the formal two-site model", *Journal of Enzyme Inhibition and Medicinal Chemistry*
  38(1) (2023) 2245168, Introduction (the conventional model binds the active site of free enzyme
  and a separate site on $ES$; operational mixed inhibition does not determine a molecular
  mechanism), Results, Cases I and IV. The restricted network explicitly omits substrate
  binding to $EI$ and catalysis by $ESI$,
  <https://doi.org/10.1080/14756366.2023.2245168>.
- The uncompetitive special case is the mechanism of J. Eilertsen, S. Schnell and S. Walcher,
  *Bulletin of Mathematical Biology* 85 (2023), article 48, <https://doi.org/10.1007/s11538-023-01150-7>; locators from the version read, arXiv:2211.10836v2 (2023), Section 6.2, Eqs. (64) and (65), <https://arxiv.org/abs/2211.10836v2>.
