# Online mechanism with arrival and departure types

In an *online mechanism design* environment each agent $i$ has type $\theta_i = (a_i, d_i, v_i)$ with arrival $a_i$, departure $d_i \ge a_i$ in a linearly ordered time domain, and value $v_i \ge 0$ for an allocation at a time in $[a_i, d_i]$. A deterministic policy allocates each agent either nothing or one time in its reported window, and is *causal* if decisions at time $t$ depend only on agents reported to arrive by $t$. Agents may misreport values and windows subject to *no early arrival* and *no late departure*. A policy is *monotone* if, the other agents' reports fixed, an allocated agent remains allocated when it reports a value at least as high together with a window at least as wide (arrival no later, departure no earlier); its *critical value* for a reported window is the infimum of the values at which it is allocated with that window ($\infty$ if there are none).

## Depends on

- [Single-parameter quasilinear mechanisms: model, DSIC and IR](../myerson-s-lemma-and-revenue-equivalence/remaining-clauses-of-single-parameter-quasilinear-mechanisms.md)

## Sources

- David C. Parkes, "Online Mechanisms", Algorithmic Game Theory, Cambridge University Press, 2007.
- Mohammad Taghi Hajiaghayi, Robert Kleinberg and David C. Parkes, "Adaptive Limited-Supply Online Auctions", Proceedings of the 5th ACM Conference on Electronic Commerce, 2004.
