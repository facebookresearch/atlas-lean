# Erasing an owned key preserves invocation priority

Let $\sigma = (\pi, r, c)$ be a service signature and $\Delta$ an ownership context such that $\pi$
is below the rank of every active capability of $\Delta$. Then for every endpoint $z$, $\pi$ is
below the rank of every active capability of $\Delta \setminus z$.
