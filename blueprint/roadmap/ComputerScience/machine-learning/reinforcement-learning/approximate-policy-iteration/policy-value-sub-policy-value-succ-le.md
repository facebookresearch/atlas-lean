# A step of approximate policy iteration loses at most 2γδ/(1−γ)

In the setting of [Error bound when approximate policy iteration stops](optimal-value-sub-policy-value-le-of-gre.md), let $\mu$ be a deterministic policy, let $J$ satisfy $|J(s) - V^{\mu}(s)| \le \delta$ for every state $s$, and let $\mu'$ be greedy with respect to $J$ ($T_{\mu'} J = T J$). Then for every state $s$

$$V^{\mu}(s) - V^{\mu'}(s) \le \frac{2\gamma\delta}{1-\gamma}.$$

With $\delta = 0$ this is the [Policy improvement theorem](../../../heuristic-search-and-planning/policy-iteration/policy-value-le-policy-value-improve.md). It is the first step of the proof of the [Error bound for approximate policy iteration](optimal-value-sub-policy-value-approx-pi.md).

## Sources

- D. P. Bertsekas, *Approximate policy iteration: a survey and some new methods*, J. Control Theory Appl. 9(3) (2011), Section 3 (the setting of Eqs. (41)–(42)).

## Background

- [One-sided contraction of a policy's Bellman operator](policy-bellman-sub-le.md): the proof bounds $T_{\mu'} V^\mu - T_{\mu'} V^{\mu'}$ by $\gamma$ times the largest loss.
