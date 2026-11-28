# Crosscurrent extraction

Assume a fixed-phase-volume model: each equilibrium contact retains a raffinate volume $V_r>0$ and uses fresh, solute-free solvent
of volume $V_s>0$, with no transfer of either carrier and no volume change. Concentrations $c_r,c_s$ are solute amount per unit
volume in the corresponding phase. Stipulate the same linear equilibrium law $c_s=Kc_r$, $K>0$, at every stage, and put
$R=V_s/V_r>0$. If $q$ is the solute amount entering a stage, its balance is
$q=V_r c_r+V_s c_s=(V_r+K V_s)c_r$. Thus the outgoing raffinate solute amount is
$q^+=q/(1+KR)$. For $N\ge0$ fresh-solvent stages with these same phase volumes and coefficient,
$q_N=q_0(1+KR)^{-N}$. For $q_0>0$ this gives the remaining fraction; for $q_0=0$ it gives zero solute without forming a ratio.

A solute-free-carrier-flow model gives the same algebra when both concentrations and $R$ use that carrier basis. A solvent-to-total-feed
mass ratio with varying output phase amounts does not in general give this formula. Harvey gives the corresponding one-step and
repeated retention fractions; this fixed-volume linear model is an explicit specialization, not a general ternary-phase extraction law.
Countercurrent extraction requires its own matched Kremser model and is outside this result.

The iteration is over the amounts after each contact, with $q_0$ the initial amount. The inverse
of $1+KR$ is raised to the natural-number stage count; at zero stages this factor is $1$.

## Sources

- David Harvey, *Analytical Chemistry 2.1*, Volume I, Chemistry LibreTexts, §7.7, "Liquid-Liquid Extractions," Eqs. (7.6) and (7.7), <https://chem.libretexts.org/Bookshelves/Analytical_Chemistry/Analytical_Chemistry_2.1_by_David_Harvey/Analytical_Chemistry_Volume_I_(Harvey)/07%3A_Obtaining_and_Preparing_Samples_for_Analysis/7.07%3A_Liquid-Liquid_Extractions>.
