# Local upper envelopes of a log-likelihood

For a log-likelihood $\ell_\theta(x)$, $\theta$ in a pseudometric space, and observations $X_0, X_1, \dots$ on a measure space with measure $P$ (expectations are integrals against $P$), write $Q(\theta) = \mathbb{E}[\ell_\theta(X_0)]$. The log-likelihood has local envelopes at $\theta$ on a set $S$ if there are measurable functions $u_n$, decreasing in $n$ and converging pointwise to $\ell_\theta$, with $\ell_{\theta'} \le u_n$ for every $\theta' \in S$ at distance less than $1/(n+1)$ from $\theta$, and $u_0(X_0)$ integrable.
