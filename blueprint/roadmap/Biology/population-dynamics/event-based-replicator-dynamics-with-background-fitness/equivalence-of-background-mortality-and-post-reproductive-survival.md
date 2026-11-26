# Equivalence of background mortality and post-reproductive survival

**Setting.** Compare two ways of adding background mortality to the event-based focal-game dynamics with strategy survival payoffs $s_i$, survivor fecundities $V_i$ and juvenile survival $1 - n/K$, without background fertility:
- *dynamics-based:* deaths from other activities occur continuously at background rate $\Psi$, giving $\dot q_i = q_i[(V_i - \bar V)(1 - n/K) + s_i - \bar s]$ and density nullcline $\tilde n_{\mathrm{dyn}} = \big(1 - \frac{\Psi + 1 - \bar s}{\bar V}\big)K$, where $\bar V = \sum_iq_iV_i$, $\bar s = \sum_iq_is_i$;
- *payoff-based:* survivors of each focal game face an extra post-reproductive survival factor $s_b$ in the same event, giving $\dot q_i = q_i[(V_i - \bar V)(1 - n/K) + s_b(s_i - \bar s)]$ and $\dot n = n[\bar V(1 - n/K) + s_b\bar s - 1]$.

**Theorem.** Suppose $s_b = 1/(1+\Psi)$ and the population is on its density nullcline. Then
1. the stationary frequency points of the two approaches coincide;
2. the payoff-based dynamics run at the rate of the dynamics-based ones divided by $1+\Psi$ (multiplied by $s_b$);
3. the stationary juvenile survival probabilities $J = 1 - \tilde n/K$ differ, with $J_{\mathrm{dyn}} = J_{\mathrm{pf}}/s_b$, so that

$$\tilde n_{\mathrm{dyn}} = \Big(1 - \frac{1 - s_b\bar s}{s_b\bar V}\Big)K.$$

## Depends on

- [Replicator dynamics from interaction rates with density-dependent recruitment](replicator-dynamics-from-interaction-rates-with-density-dependent-recruitment.md)

## Expansion

On the payoff-based nullcline $1 - n/K = (1 - s_b\bar s)/\bar V$, and on the dynamics-based one $1 - n/K = (1 + \Psi - \bar s)/\bar V = (1 - s_b\bar s)/(s_b\bar V)$ when $1 + \Psi = 1/s_b$; substituting into the frequency equations shows that the payoff-based right-hand side is $s_b$ times the dynamics-based one, which gives parts 1 and 2. Thus, for static questions (which frequencies are stable), continuous background mortality can be replaced by the probability $d_b = \Psi/(1+\Psi)$ of dying between two focal interactions, an empirically measurable quantity; but because the two schemes distribute deaths differently in time, population sizes and transient dynamics differ, increasingly so for large background mortality.

## Sources

- K. Argasinski, M. Broom, "Interaction rates, vital rates, background fitness and replicator dynamics: how to embed evolutionary game structure into realistic population dynamics", Theory in Biosciences 137(1) (2018) 33–50, Two distinct approaches to background fitness, Eqs (9)–(11), and Appendix 2, Theorem 1 (Eq (31)), <https://doi.org/10.1007/s12064-017-0257-y>, PMCID PMC5893772.
