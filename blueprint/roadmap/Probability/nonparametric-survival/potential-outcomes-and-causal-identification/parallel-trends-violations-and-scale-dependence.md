# Violations of parallel trends and their dependence on the outcome scale

Consider two groups $g \in \{T, C\}$ observed in periods $0$ and $1$, with the treated group $T$ treated in period $1$ only, and let $\mu_{g,t}$ be the mean untreated outcome. The difference-in-differences estimand $(\bar Y_{T,1} - \bar Y_{T,0}) - (\bar Y_{C,1} - \bar Y_{C,0})$ equals the average effect on the treated in period $1$ when $\mu_{T,1} - \mu_{T,0} = \mu_{C,1} - \mu_{C,0}$.

(A violation.) With deterministic outcomes, untreated means $\mu_{C,0} = \mu_{C,1} = 0$, $\mu_{T,0} = 0$, $\mu_{T,1} = 1$, and zero treatment effect, the estimand is $1$ while the effect on the treated is $0$.

(Levels versus logarithms.) With deterministic positive untreated outcomes $1 \to 2$ in group $C$ and $2 \to 3$ in group $T$, untreated trends are parallel in levels (both rise by $1$) but not in logarithms ($\log 2 \ne \log(3/2)$). So the identifying assumption can hold on one scale and fail on another. When parallel trends holds for every strictly monotone transformation is characterized in the cited paper; that characterization is not part of this statement.

## Sources

- J. Roth and P. H. C. Sant'Anna, "When is parallel trends sensitive to functional form?", *Econometrica* 91(2):737–747, 2023, arXiv:2010.04814, abstract and §1
