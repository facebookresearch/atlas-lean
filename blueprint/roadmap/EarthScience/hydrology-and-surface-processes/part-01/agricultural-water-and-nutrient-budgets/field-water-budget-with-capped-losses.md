# Field water budget with capped losses

Let the soil-water depth $S$ satisfy $S' = P + I - \mathrm{ET}_a - \mathrm{RO} - \mathrm{DR}$ with continuous nonnegative precipitation
$P$, irrigation $I$, potential evapotranspiration $E_p$ and potential runoff $R_p$, time constants $\tau_E, \tau_R > 0$, $k_D \ge 0$ and
field capacity $S_{fc} \ge 0$, where $\mathrm{ET}_a = \min(E_p, \max(S, 0)/\tau_E)$, $\mathrm{RO} = \min(R_p, \max(S, 0)/\tau_R)$ and
$\mathrm{DR} = k_D\max(S - S_{fc}, 0)$. The right side is continuous in time and globally Lipschitz in $S$, so solutions exist and are
unique; all losses vanish at $S = 0$, so a solution with $S(0) \ge 0$ stays nonnegative. Multiplying by a fixed positive area gives
volume budgets. The model does not force $S \le S_{fc}$. Crop-yield response is outside this result.

## Depends on

## Proof depends on

## Sources

- R. G. Allen, L. S. Pereira, D. Raes and M. Smith, *Crop Evapotranspiration*, FAO Irrigation and Drainage Paper 56, 1998, Chapter 8, the soil water stress coefficient (Equations 80–81) and the root-zone water balance (Equations 85 and 88), <https://www.fao.org/3/x0490e/x0490e0e.htm>.
