# A first error short-circuits a bind

For every computation $m$, continuation $k$ and exception $e$: if $\mathrm{run}(m) = \mathrm{error}(e)$, then $\mathrm{run}(m \mathbin{>\!\!>\!=} k) = \mathrm{error}(e)$. The same error is returned and the continuation is not run.
