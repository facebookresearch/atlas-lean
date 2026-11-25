# One-way analysis of variance F test

Let $\iota$ be a finite index set of $n$ observations, $g : \iota \to G$ an assignment to a finite set of groups with every group nonempty, and $X = (X_i)_{i \in \iota}$ i.i.d. $\mathcal N(\mu_0, v)$ on a probability space with $v > 0$ (all group means equal). With group means $\bar X_h$ and grand mean $\bar X$, write $\mathrm{SSB} = \sum_i(\bar X_{g(i)} - \bar X)^2$ and $\mathrm{SSW} = \sum_i(X_i - \bar X_{g(i)})^2$. If $|G| \ge 2$ and $n > |G|$, then the observable statistic $\dfrac{\mathrm{SSB}/(|G| - 1)}{\mathrm{SSW}/(n - |G|)}$ has Snedecor's $F$ law with $(|G| - 1, n - |G|)$ degrees of freedom.

## Sources

- G. Casella and R. L. Berger, *Statistical Inference*, 2nd ed., Duxbury (2002), §11.2.
