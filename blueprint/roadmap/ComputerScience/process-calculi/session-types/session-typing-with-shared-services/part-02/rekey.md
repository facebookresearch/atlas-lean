# Rekeying preserves shared invocation priority

Let $\sigma = (\pi, r, c)$ be a service signature, $\Delta$ an ownership context and $f$ a map from
names to names such that $x^{r'} \mapsto f(x)^{r'}$ is injective on the domain of $\Delta$. If $\pi$
is below the rank of every active capability of $\Delta$, then it is below the rank of every active
capability of $f_*\Delta$.
