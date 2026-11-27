# Run From append

For a strategy $A$, any prior history $h$ and request lists $\sigma$ and $\tau$, the run from $h$ on $\sigma \mathbin{+\!\!+} \tau$ is the run from $h$ on $\sigma$ followed by the run from $h \mathbin{+\!\!+} \sigma$ on $\tau$: $\mathrm{runFrom}(A, h, \sigma \mathbin{+\!\!+} \tau) = \mathrm{runFrom}(A, h, \sigma) \mathbin{+\!\!+} \mathrm{runFrom}(A, h \mathbin{+\!\!+} \sigma, \tau)$. In particular the run on a prefix is the corresponding prefix of the run on any extension.
