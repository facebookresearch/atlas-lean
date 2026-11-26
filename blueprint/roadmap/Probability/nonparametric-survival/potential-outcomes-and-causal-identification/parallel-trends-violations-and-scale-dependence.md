# Violations of parallel trends and their dependence on the outcome scale

Consider two groups $g \in \{T,C\}$ of positive probability in periods $0$ and $1$, with group $T$ treated only in period $1$. For observed group means $\bar Y_{g,t}$, the population difference-in-differences is $(\bar Y_{T,1}-\bar Y_{T,0})-(\bar Y_{C,1}-\bar Y_{C,0})$. The untreated trends are parallel on a given outcome scale when the group mean changes on that scale are equal.

**A violation.** In both groups, set both pre-period potential outcomes to zero. Set both post-period potential outcomes to one in $T$ and zero in $C$. The treatment effect is zero for every unit, but the observed difference-in-differences is $1$ and the average treatment effect in $T$ is $0$.

**Levels versus logarithms.** Take deterministic positive untreated outcomes $1\to 2$ in $C$ and $2\to 3$ in $T$. The untreated trends are parallel in levels, since both rise by $1$. In logs the treated-group trend is $\log(3/2)$ and the control-group trend is $\log 2$. Thus the difference-in-differences contrast of the untreated outcomes is zero in levels and strictly negative in logs.

## Background

- [Identification of the average effect on the treated by difference-in-differences](../../not-yet-classified/part-04/difference-in-differences/did-estimand-observed-eq-att-post.md): under no anticipation and parallel trends for the untreated outcomes, the observed difference-in-differences identifies the post-period average effect on the treated.

## Sources

- J. Roth and P. H. C. Sant'Anna, "When is parallel trends sensitive to functional form?", *Econometrica* 91(2):737–747, 2023, arXiv:2010.04814, §§1 and 3: the role of the outcome scale and the general characterization of invariance under monotone transformations. The two numerical examples above are derived here.
