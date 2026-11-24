# Inserting a completed entry preserves invocation priority

Let $\sigma = (\pi, r, c)$ be a service signature, $\Delta$ an ownership context such that $\pi$ is
below the rank of every active capability of $\Delta$, $z$ an endpoint and $u$ a capability whose
protocol has head $\mathrm{end}$. Then $\pi$ is below the rank of every active capability of
$\Delta[z \mapsto u]$.
