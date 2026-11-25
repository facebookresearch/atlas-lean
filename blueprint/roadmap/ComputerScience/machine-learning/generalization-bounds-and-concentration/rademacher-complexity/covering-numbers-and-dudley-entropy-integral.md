# Covering numbers and Dudley entropy integral

This node collects covering-number bounds on empirical Rademacher complexity.

## Expansion

A sound expansion has separate pages for:

1. **Conventions.** For a class $F$ of real functions and a sample $S = (z_1, \dots, z_m)$, the empirical
   metric is $d_S(f, g) = (\frac1m \sum_i (f(z_i) - g(z_i))^2)^{1/2}$, $N(F, \varepsilon)$ is the least size of an
   $\varepsilon$-cover in $d_S$, and the empirical Rademacher complexity is
   $\mathbb{E}_\sigma \sup_{f \in F} \frac1m \sum_i \sigma_i f(z_i)$.
2. **Single-scale bound.** For every $\varepsilon > 0$, the Rademacher complexity is at most
   $\varepsilon + D\sqrt{2 \log N(F, \varepsilon)/m}$ with $D$ the $d_S$-diameter of $F$ (natural logarithm; translate $F$ by
   one of its members, which changes neither side).
3. **Dudley's chaining bound.** If every $f \in F$ takes values in $[-1, 1]$ on the sample and $F$ contains the zero
   function, the Rademacher complexity is at most
   $\inf_{\alpha > 0} \bigl(4\alpha + \frac{12}{\sqrt m} \int_\alpha^{1/2} \sqrt{\ln N(F, \varepsilon)}\, d\varepsilon\bigr)$.

## Depends on

- [Rademacher complexity](rademacher-complexity.md)

## Proof depends on

- [Massart's finite-class lemma](rademacher-complexity-le-of-finite.md)

## Sources

- M. Telgarsky, *Deep learning theory lecture notes*, Theorem 15.1 (single scale) and Theorem 15.2 (Dudley), stated for the unnormalized Rademacher complexity of $U \subseteq [-1,1]^n$ with $0 \in U$ and unnormalized Euclidean covers; dividing by $n = m$ and rescaling the radius by $\sqrt m$ gives items 2 and 3. <https://mjt.cs.illinois.edu/dlt/>
