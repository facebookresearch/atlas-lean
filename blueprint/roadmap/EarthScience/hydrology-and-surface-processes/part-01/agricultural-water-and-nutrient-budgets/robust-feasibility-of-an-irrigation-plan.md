# Robust feasibility of an irrigation plan

On a finite horizon let the soil water evolve as $S_{k+1} = S_k + I_k + w_k$, with disturbances in forecast bounds
$w_{\mathrm{lo},k} \le w_k \le w_{\mathrm{hi},k}$ and $S_0 \in [S_{\min}, S_{\max}]$. A robust irrigation choice satisfies
$0 \le I_k \le I_{\mathrm{cap}}$ and $S_{\min} - S_k - w_{\mathrm{lo},k} \le I_k \le S_{\max} - S_k - w_{\mathrm{hi},k}$. If this set is
nonempty at every step, choosing from it keeps $S_k \in [S_{\min}, S_{\max}]$ for every disturbance within the bounds, by induction. A
drought or heavy rain can make the set empty. Any cumulative allocation quota is an additional constraint, and the validity of the
forecast bounds is an assumption. Optimizing the plan is outside this result.

## Depends on

## Proof depends on

## Sources

- R. G. Allen, L. S. Pereira, D. Raes and M. Smith, *Crop Evapotranspiration*, FAO Irrigation and Drainage Paper 56, 1998, Chapter 8, the soil water stress coefficient (Equations 80–81) and the root-zone water balance (Equations 85 and 88), <https://www.fao.org/3/x0490e/x0490e0e.htm>.
