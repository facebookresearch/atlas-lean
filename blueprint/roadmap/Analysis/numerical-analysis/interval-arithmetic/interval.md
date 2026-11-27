# Interval

For a type $\alpha$ with an order $\le$, a *nonempty interval* of $\alpha$ is a pair $(a, b)$ of elements of $\alpha$ with $a \le b$; two nonempty intervals are equal when their endpoints are equal. When $\le$ is a partial order, a nonempty interval is regarded as the set $[a, b] = \{x \in \alpha : a \le x \le b\}$, and this identification is injective. For $\alpha = \mathbb{R}$ these are the nonempty, closed and bounded sets of reals $[a, b]$ with $a \le b$, the *intervals* of interval arithmetic; a *point interval* is $[a, a]$.

## Sources

- T. Hickey, Q. Ju and M. H. van Emden, "Interval arithmetic: from principles to implementation", *Journal of the ACM* 48(5):1038–1068, 2001, Section 2, Definition 2 (a real interval is a closed connected set of reals) and Theorem 1 (the closed connected sets of reals, of which the bounded nonempty ones are the sets $[a, b]$ with $a \le b$). <https://doi.org/10.1145/502102.502106>
- Mathlib, `Mathlib/Order/Interval/Basic.lean`: the structure `NonemptyInterval` and its injective coercion to `Set.Icc`.
