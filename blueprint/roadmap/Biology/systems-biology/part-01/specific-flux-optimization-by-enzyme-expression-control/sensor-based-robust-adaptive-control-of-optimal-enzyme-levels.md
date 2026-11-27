# Sensor-based robust adaptive control of optimal enzyme levels

**Setting.** A metabolic network has stoichiometric matrix $N$, internal metabolite concentrations $x_I$, external concentrations $x_E$ and reactions $j=1,\dots,m$ with rates $v_j=e_jf_j(x_I;x_E)$, where $e_j$ is the enzyme concentration and $f_j$ the enzyme-specific rate law. For a fixed output reaction $r$, the specific flux is $v_r/e_T$ with total enzyme $e_T=\sum_je_j$.

Fix an elementary flux mode with flux vector $(V_1,\dots,V_m)$, the cost $O(x_I)=\sum_jV_j/f_j(x_I;x_E)$ and growth rate $\mu$.

**qORAC (Definition 1).** Choose a set $S$ of internal sensor metabolites. For sensor values $x_S$, let $\xi(x_S)=(\xi_I(x_S),\xi_E(x_S))$ solve

$$\xi_S=x_S,\qquad \frac{\partial O}{\partial\xi_i}(\xi)=0\quad(i\in I),$$

i.e. the internal and external concentrations for which the current sensor values would be optimal. The controlled system is

$$\dot x_i=\sum_jN_{ij}e_jf_j(x_I;x_E),\qquad \dot e_j=E_j(x_S)-\mu e_j,\qquad E_j(x_S)=\mu\,\frac{V_j/f_j(\xi(x_S))}{\sum_lV_l/f_l(\xi(x_S))}.$$

**Properties.**
- $\xi(x_S)$ is well defined by the implicit function theorem only if the number of sensors equals the number of independently varying external parameters (nutrient levels, temperature, pH and the like) to which the optimum must adapt.
- At any steady state, $e_j\propto V_j/f_j(\xi(x_S))$ and the predicted optimum coincides with the actual state, so a qORAC steady state is the specific-flux optimum for the current environment; the source proves that this steady state is unique for linear enzyme chains (Supporting Information, Theorem 3).

## Depends on

- [Specific flux maximization as enzyme cost minimization over metabolites](specific-flux-maximization-as-enzyme-cost-minimization-over-metabolites.md)

## Expansion

The gene network cannot read $x_E$, so it solves the optimality relations with the sensor concentrations prescribed instead and treats the external concentrations as unknowns. If the enzyme levels it then synthesizes are not those of a steady state, metabolites and therefore sensors keep changing, and so do the predicted optimal enzyme levels; only the optimal state is self-consistent. The normalization of $E_j$ fixes total enzyme at $1$ and keeps synthesis rates positive even for reversed fluxes and near thermodynamic equilibrium.

## Sources

- R. Planqué, J. Hulshof, B. Teusink, J. C. Hendriks, F. J. Bruggeman, "Maintaining maximal metabolic flux by gene expression control", PLoS Computational Biology 14 (2018) e1006412. <https://doi.org/10.1371/journal.pcbi.1006412>, PMCID PMC6168163. Steps 3–4 and Definition 1, Eqs. (12)–(18).
