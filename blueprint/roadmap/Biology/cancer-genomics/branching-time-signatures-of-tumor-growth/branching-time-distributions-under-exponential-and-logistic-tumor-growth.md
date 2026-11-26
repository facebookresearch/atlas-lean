# Branching-time distributions under exponential and logistic tumor growth

**Setting.** A tumor grows from one cell by a continuous-time birth–death process observed at time $T$, and $m$ cells are sampled; the internal branching times $\tau_{S,i}$ of the reconstructed sample genealogy are studied through a coalescent point process (CPP) approximation for large $T$ and $m$. In the exponential model birth and death rates are constant. In the logistic models the rates depend on population size with carrying capacity $\kappa$, initial net growth rate $r_0$ and initial birth rate $\lambda_0$, and $\lambda(\kappa)$ is the birth rate at carrying capacity; let $f_T$ be the marginal branching-time density on $[0, T]$ and $I_T$ its unnormalised form. Put $A = \lambda_0(\kappa - 1)/\lambda(\kappa)$ and $B = r_0\kappa/(m\lambda(\kappa))$.

**Theorem.**
1. *(Exponential growth.)* Under the exponential-growth CPP approximation the marginal density of each branching time is log-concave, hence unimodal, with mode near the root.
2. *(Logistic growth.)* If $A > 20$ and $10 < B < A/2$ (mild for large $\kappa$ and sparse sampling $1 \ll m \ll \kappa$), there are times $0 < T_1 < T_2 < T_3$ such that:
   - for $T < T_1$, $I_T$ is increasing, with a single mode at the recent endpoint $t = T$;
   - for $T_1 < T < T_2$, $I_T$ has exactly one interior local maximum;
   - for $T_2 < T < T_3$, $I_T$ is bimodal: an interior maximum, an interior minimum and a boundary maximum at $t = T$;
   - for $T > T_3$, there is no interior maximum; for each fixed $a \ge 0$, $I_T(T - a) \to \dfrac{\lambda(\kappa) m^2/\kappa}{(1 + \lambda(\kappa) m a/\kappa)^2}$ and $I_T(0)/I_T(T) \to 0$, and $\int_0^{(1-\eta)T} f_T \to 0$ for every $\eta \in (0,1)$, so branching times concentrate near the present.

## Expansion

In exponential growth almost all coalescences of a sparse sample happen early, when the population was small, giving a single early mode. Under logistic growth the population first expands (early coalescences), then saturates at $\kappa$, where it behaves like a constant-size population with turnover rate $\lambda(\kappa)$ and coalescences accumulate at a rate set by $\lambda(\kappa)/\kappa$; recent coalescences therefore grow in weight with time since initiation. The CPP density can be written explicitly through the deterministic trajectory with time-dependent effective rates, and tracking its critical points yields the sequence expansion-dominated, early–recent bimodal and recent-dominated phases, a signature of growth constraints detectable from inferred tumor phylogenies.

## Sources

- M. Wang, Z. Weng, J. Foo, Z. Wang, "Branching-Time Signatures of Growth Regime in Tumor Birth-Death Models", arXiv:2607.11011 (2026), Theorems 1 and 2, <https://doi.org/10.48550/arXiv.2607.11011>.
