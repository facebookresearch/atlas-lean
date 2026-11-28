# Metric election and distortion of a voting rule

Let $V$ be a finite set of $n$ voters and $C$ a finite set of $m$ candidates. A metric on $V \cup C$ is a function $d$ that is nonnegative, symmetric, satisfies the triangle inequality and has $d(x, x) = 0$; distinct points may be at distance $0$ (a pseudometric). A ranking profile $\sigma = (\succ_v)_{v \in V}$ of strict orders on $C$ is consistent with $d$ if $d(v, a) < d(v, b)$ implies $a \succ_v b$. The social cost of a candidate is $\mathrm{SC}(c, d) = \sum_{v \in V} d(v, c)$. The distortion of a deterministic rule $f$ mapping profiles to candidates is

$$
\mathrm{dist}(f) = \sup_{\sigma} \; \sup_{d \text{ consistent with } \sigma} \frac{\mathrm{SC}(f(\sigma), d)}{\min_{c \in C} \mathrm{SC}(c, d)},
$$

with $0/0 := 1$; for a randomized rule returning a distribution on $C$, the numerator is the expected social cost.

## Sources

- E. Anshelevich, O. Bhardwaj, E. Elkind, J. Postl, P. Skowron, "Approximating optimal social choice under metric preferences", Artificial Intelligence 264 (2018); AAAI 2015.
