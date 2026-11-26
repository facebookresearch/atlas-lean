# Oil reservoir material balance with dissolved gas

Consider an oil reservoir with no aquifer, constant pore volume $V_p$ and constant water volume $W$, initial stock-tank oil $N > 0$,
initial free gas $G_{fi} \ge 0$ and initial solution gas-oil ratio $R_{si}$, and formation volume factors $B_o(p), B_g(p) > 0$ and
solution ratio $R_s(p) \ge 0$ on a declared domain, in common units. After producing oil $0 \le N_p \le N$ and total gas $G_p \ge 0$,
the remaining free gas is $G_f = N R_{si} + G_{fi} - G_p - (N - N_p) R_s(p)$, and the volume balance is

$$V_p - W = (N - N_p) B_o(p) + G_f B_g(p) = N B_{oi} + G_{fi} B_{gi},$$

which is equivalent to the material-balance residual
$(N - N_p) B_o + (N R_{si} + G_{fi} - G_p - (N - N_p) R_s) B_g - N B_{oi} - G_{fi} B_{gi} = 0$. Only histories with $N - N_p \ge 0$ and
$G_f \ge 0$ are admissible. Phase-equilibrium models for $B_o$, $B_g$ and $R_s$ are outside this result.

## Depends on

## Proof depends on

## Expansion

Open a source for the black-oil material balance with dissolved gas and check this lumped form and its sign conventions against it.

## Sources

- R. J. Schilthuis, Active oil and reservoir energy, *Transactions of the AIME* 118 (1936) 33–52.
