# Rademacher generalization bound for bounded function classes

For a class $F$ of functions $Z \to \mathbb{R}$ and a sample $S = (z_1, \dots, z_m)$, write $\hat{R}_S(F) = \mathbb{E}_\sigma \sup_{f \in F} \frac{1}{m}\sum_i \sigma_i f(z_i)$ with independent uniform signs $\sigma_i$, and $R_m(F) = \mathbb{E}_{S \sim D^m}\hat{R}_S(F)$. Let $Z$ be finite, $D$ a probability distribution on $Z$, $F$ a class of functions with values in $[a, b]$, $m > 0$ and $\delta \in (0,1)$. Then $\mathbb{E}_S \sup_{f\in F}(\mathbb{E}_D f - \hat{\mathbb{E}}_S f) \le 2R_m(F)$, and with probability at least $1 - \delta$ over $S \sim D^m$, every $f \in F$ satisfies

$$
\mathbb{E}_D f \le \hat{\mathbb{E}}_S f + 2R_m(F) + (b - a)\sqrt{\frac{\ln(1/\delta)}{2m}},
$$

and, with probability at least $1-\delta$, also the data-dependent bound $\mathbb{E}_D f \le \hat{\mathbb{E}}_S f + 2\hat{R}_S(F) + 3(b-a)\sqrt{\ln(2/\delta)/(2m)}$. For a finite class with values in $[0,1]$, Massart's lemma gives $\mathbb{E}_D f \le \hat{\mathbb{E}}_S f + 2\sqrt{2\ln|F|/m} + \sqrt{\ln(1/\delta)/(2m)}$.

## Proof sketch

Symmetrization with a ghost sample and random signs bounds the expected worst-case gap by $2R_m(F)$. McDiarmid's bounded-differences inequality (each example changes the gap by at most $(b-a)/m$) gives the first bound; for the data-dependent form, apply McDiarmid also to $\hat{R}_S(F)$ and combine at confidence $\delta/2$ each.

## Depends on

- [Empirical Rademacher complexity](../rademacher-complexity/rademacher-complexity.md)
- [The Rademacher risk bound](../rademacher-complexity/risk-le-empirical-add-rademacher.md)

## Proof depends on

- [Concentration of the uniform deviation](../bounded-differences-uniform-deviation.md)
- [Massart's finite-class lemma](../rademacher-complexity/rademacher-complexity-le-of-finite.md)

## Sources

- M. Mohri, A. Rostamizadeh and A. Talwalkar, "Foundations of Machine Learning", 2nd edition, MIT Press, 2018.
- S. Shalev-Shwartz and S. Ben-David, "Understanding Machine Learning: From Theory to Algorithms", Cambridge University Press, 2014.
- P. L. Bartlett and S. Mendelson, "Rademacher and Gaussian Complexities: Risk Bounds and Structural Results", Journal of Machine Learning Research, 2002.
