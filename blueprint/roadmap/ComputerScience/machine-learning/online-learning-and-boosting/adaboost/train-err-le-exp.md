# AdaBoost drives the training error down exponentially

Let AdaBoost run on $m > 0$
training points with labels $y$ and a weak learner with edge $\gamma \ge 0$, that is, one that on
every weighting $D$ of the training points with $D_i > 0$ for all $i$ and $\sum_i D_i = 1$ returns
a hypothesis whose weighted error under $D$ lies in $(0, 1/2 - \gamma]$. Then for every number of
rounds $T$, the training error after $T$ rounds is at most $e^{-2\gamma^2 T}$.

With per-round edges the exponent becomes $-2 \sum_t \gamma_t^2$: see [AdaBoost's training error in terms of the edges](train-err-le-exp-sum-sq.md).

## Sources

- Y. Freund and R. E. Schapire, "A decision-theoretic generalization of on-line learning and an application to boosting", *J. Comput. System Sci.* 55 (1997), 119–139, equations (21) and (22).
