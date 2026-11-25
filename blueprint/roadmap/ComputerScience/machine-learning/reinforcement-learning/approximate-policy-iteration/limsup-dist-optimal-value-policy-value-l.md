# Asymptotic error bound for approximate policy iteration

Under the hypotheses of the [Error bound for approximate policy iteration](optimal-value-sub-policy-value-approx-pi.md), and with at least one state,

$$\limsup_{k\to\infty} \|V^* - V^{\mu_k}\|_\infty \le \frac{2\gamma\delta}{(1-\gamma)^2}.$$

Approximate policy iteration need not converge: the policies may oscillate. The bound says that they eventually stay within $2\gamma\delta/(1-\gamma)^2$ of optimal. The survey notes that the bound is tight in theory but usually conservative in practice. When the method stops, the sharper [Error bound when approximate policy iteration stops](optimal-value-sub-policy-value-le-of-gre.md) applies.

## Sources

- D. P. Bertsekas, *Approximate policy iteration: a survey and some new methods*, J. Control Theory Appl. 9(3) (2011), 310–335, Eq. (42).
