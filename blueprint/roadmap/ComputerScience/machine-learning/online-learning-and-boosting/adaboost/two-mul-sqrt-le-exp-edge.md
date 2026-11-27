# A round's factor is at most $e^{-2\gamma^2}$ for its own edge

For every real $\varepsilon$, with $\gamma = 1/2 - \varepsilon$,

$$2 \sqrt{\varepsilon (1 - \varepsilon)} \le e^{-2 \gamma^2},$$

where the square root of a negative number is $0$. It follows from $1 - 4\gamma^2 \le e^{-4 \gamma^2}$. Unlike [the uniform-edge estimate](two-mul-sqrt-le-exp.md), no sign condition on $\gamma$ is needed: a round with $\varepsilon > 1/2$ has the same factor as the round with error $1 - \varepsilon$.

## Sources

- Y. Freund and R. E. Schapire, "A decision-theoretic generalization of on-line learning and an application to boosting", *J. Comput. System Sci.* 55 (1997), 119–139, equation (21), the final inequality.
