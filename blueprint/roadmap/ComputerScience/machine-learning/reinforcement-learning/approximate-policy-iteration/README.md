# Approximate policy iteration

Error bounds for policy iteration with inexact policy evaluation, following Bertsekas's survey *Approximate policy iteration: a survey and some new methods* (J. Control Theory Appl. 9(3), 2011, Section 3). Each step evaluates the current policy up to a sup-norm error $\delta$ and acts greedily on the estimate. If the method stops, the final policy is within $2\gamma\delta/(1-\gamma)$ of optimal; in general the iterates come within $2\gamma\delta/(1-\gamma)^2$ of optimal asymptotically, with an explicit geometric transient. Finite states and actions, discount $0 \le \gamma < 1$, rewards maximized.

- [Error bound when approximate policy iteration stops](optimal-value-sub-policy-value-le-of-gre.md)
- [A step of approximate policy iteration loses at most 2γδ/(1−γ)](policy-value-sub-policy-value-succ-le.md)
- [Error bound for approximate policy iteration](optimal-value-sub-policy-value-approx-pi.md)
- [Asymptotic error bound for approximate policy iteration](limsup-dist-optimal-value-policy-value-l.md)
- [One-sided contraction of a policy's Bellman operator](policy-bellman-sub-le.md)

## Related topics

- [Policy iteration](../../../heuristic-search-and-planning/policy-iteration/README.md)
- [Greedy policies of approximate values](../greedy-policies-of-approximate-values/README.md)
- [Value iteration](../../../heuristic-search-and-planning/value-iteration/README.md)
