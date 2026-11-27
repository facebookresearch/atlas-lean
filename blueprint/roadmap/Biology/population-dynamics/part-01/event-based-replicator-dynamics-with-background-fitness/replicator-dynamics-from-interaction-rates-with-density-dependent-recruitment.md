# Replicator dynamics from interaction rates with density-dependent recruitment

**Event-based growth.** Events of type $i$ occur to each individual as independent Poisson processes at rate $\tau^i$, producing on average $W^i$ newborns and killing the participant with probability $d^i$; the population size obeys

$$\dot n = \sum_i n\,\tau^i\big(W^i - d^i\big),$$

so $\tau^iW^i$ and $\tau^id^i$ are the per-capita fertility and mortality rates of event type $i$.

**Focal game with background events.** Single out a focal game played at rate $\tau_F$ and aggregate all other events into a background class with rate $\tau_B = \sum_i\tau_B^i$, mean fertility $W_B$ and mean death probability $d_B$. In the focal game a strategy-$i$ individual survives with probability $s_i(q)$ and its survivors produce $V_i(q) = \sum_j q_js_i(e_j)W_i(e_j)$ offspring, where $q$ is the vector of strategy frequencies; newborns are recruited with density-dependent juvenile survival $1 - n/K$. After rescaling time by $\tau_F$ and writing $\theta = \tau_B/\tau_F$, $\Phi = \theta W_B$, $\Psi = \theta d_B$:

**Proposition.** The strategy frequencies $q_i = n_i/n$ and population size satisfy

$$\dot q_i = q_i\Big[\Big(V_i - \sum_jq_jV_j\Big)\Big(1 - \frac nK\Big) + s_i - \sum_jq_js_j\Big],$$

$$\dot n = n\Big[\Big(\Phi + \sum_iq_iV_i\Big)\Big(1 - \frac nK\Big) + \sum_iq_is_i - 1 - \Psi\Big],$$

and for fixed $q$ the population size is attracted to the density nullcline

$$\tilde n = \Big(1 - \frac{\Psi + 1 - \sum_iq_is_i}{\Phi + \sum_iq_iV_i}\Big)K.$$

## Depends on

- [Replicator Field](../../stability-of-boundary-evolutionarily-stable-stra/replicator-field.md)

## Expansion

Each strategy's growth rate is $V_i(1-n/K) - (1-s_i) + \Phi(1 - n/K) - \Psi$; background terms are the same for all strategies, so they cancel in the frequency equation and affect selection only through the population size $n$, which enters the frequency dynamics via the recruitment factor $1 - n/K$. The ratio $\theta$ is the mean number of background events between two focal games; letting $\theta \to \infty$ (rare focal games) is the weak-selection limit in which the game's feedback on ecology vanishes. Unlike a constant added to a payoff matrix, background fertility and mortality enter as separate demographic rates, and they shift the density nullcline and hence the strength of density-dependent selection.

## Sources

- K. Argasinski, M. Broom, "Interaction rates, vital rates, background fitness and replicator dynamics: how to embed evolutionary game structure into realistic population dynamics", Theory in Biosciences 137(1) (2018) 33–50, The general model, Eqs (1)–(8), <https://doi.org/10.1007/s12064-017-0257-y>, PMCID PMC5893772.
