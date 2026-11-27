# One-way analysis of variance

Let $\iota$ be a finite index set, $\mathrm{grp} : \iota \to G$ a labelling by a finite set of groups, and $x_i$, $i \in \iota$, i.i.d. $N(\mu, v)$ observations. With $\bar x_g$ the [group means](group-mean.md) and $\bar x = \frac{1}{|\iota|}\sum_j x_j$, the between-group sum of squares $\sum_i (\bar x_{\mathrm{grp}(i)} - \bar x)^2$ is independent of the within-group sum of squares $\sum_i (x_i - \bar x_{\mathrm{grp}(i)})^2$.
