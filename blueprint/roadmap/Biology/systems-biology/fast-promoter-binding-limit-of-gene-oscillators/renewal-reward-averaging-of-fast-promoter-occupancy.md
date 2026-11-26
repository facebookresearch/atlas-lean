# Renewal-reward averaging of fast promoter occupancy

Consider a transcription-translation oscillator in which the regulatory site of gene $1$ is occupied ($X_1 = 1$) or free ($X_1 = 0$) by a repressor homodimer of concentration $D_2(t)$. For a small time-scale parameter $\varepsilon > 0$ the site switches as a two-state Markov process with

$$\Pr\{X_1 = 0 \text{ on } (t, t+h) \mid X_1(t) = 0\} = e^{-D_2(t) h/\varepsilon} + o(h), \qquad \Pr\{X_1 = 1 \text{ on } (t, t+h) \mid X_1(t) = 1\} = e^{-r h/\varepsilon} + o(h),$$

so binding is proportional to the dimer concentration and the mean bound time $\varepsilon/r$ is state independent. The continuous variables obey mass-action ODEs driven by the site states, for example

$$R_1' = k_{13}\,(1 - X_1) - k_{14} R_1, \qquad P_1' = k_{15} R_1 - k_{16} P_1 - 2k_{17} P_1^2 + 2k_{18} D_1, \qquad D_1' = k_{17} P_1^2 - k_{18} D_1,$$

and symmetrically for gene $2$ (site $Y_1$ occupied by $D_1$, unbinding rate $s/\varepsilon$). Let $(R_1^\varepsilon, P_1^\varepsilon, D_1^\varepsilon, \dots)$ be a sample path of this piecewise-deterministic process and $(R_1, P_1, D_1, \dots)$ the solution, from the same initial data, of the **averaged system** in which each site indicator is replaced by its quasi-stationary mean:

$$R_1' = k_{13}\,\frac{r}{r + D_2} - k_{14} R_1, \qquad R_2' = k_{13}\,\frac{s}{s + D_1} - k_{14} R_2,$$

the remaining equations unchanged.

**Proposition.** Almost surely, for every $t > 0$, $R_1^\varepsilon(t) \to R_1(t)$, $P_1^\varepsilon(t) \to P_1(t)$, $D_1^\varepsilon(t) \to D_1(t)$, $R_2^\varepsilon(t) \to R_2(t)$, and so on for all continuous variables, as $\varepsilon \to 0$.

The averaged repression term $r/(r + D_2)$ is a hyperbolic (Michaelis–Menten type) occupancy function; an activating site occupied by a heterodimer $D_{13}$ with unbinding rate $q/\varepsilon$ averages to $D_{13}/(q + D_{13})$.

## Expansion

If $D_2$ were constant, the site alternates free periods, exponential with mean $\varepsilon/D_2$, and bound periods, exponential with mean $\varepsilon/r$. Taking the bound time as the reward of each cycle, the renewal-reward theorem gives the almost-sure long-run fraction of bound time $E(\text{reward})/E(\text{cycle length}) = (\varepsilon/r)/(\varepsilon/r + \varepsilon/D_2) = D_2/(r + D_2)$, independent of $\varepsilon$; as $\varepsilon \to 0$ this average is achieved on every macroscopic interval. The rigorous proof writes $R_1^\varepsilon(t) = R_1(0)e^{-k_{14}t} + k_{13}\int_0^t (1 - X_1^\varepsilon)(\tau)\, e^{k_{14}(\tau - t)}\,d\tau$, uses equicontinuity of the continuous variables to extract convergent subsequences, freezes the slowly varying $D_2$ on a partition of mesh $\Delta$, applies the renewal-reward limit on each subinterval to show $\int_s^t (1 - X_1^\varepsilon) f\,d\tau \to \int_s^t \frac{r}{r + D_2} f\,d\tau$ up to $O(\Delta)$, and lets $\Delta \to 0$; uniqueness for the averaged ODE identifies every subsequential limit. In the model, two such ultradian oscillators with slightly different periods drive a fifth gene through a heterodimer, producing circadian beats robust to the choice of $\varepsilon$.

## Sources

- R. Edwards, R. Gibson, R. Illner and V. Paetkau, "A stochastic model for circadian rhythms from coupled ultradian oscillators", Theoretical Biology and Medical Modelling 4 (2007) 1, Eqs. (1)–(12) and Proposition 1 with proof, <https://doi.org/10.1186/1742-4682-4-1>, PMCID PMC1794229.
