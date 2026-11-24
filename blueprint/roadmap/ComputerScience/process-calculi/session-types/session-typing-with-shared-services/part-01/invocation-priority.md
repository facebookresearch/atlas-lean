# Priority of a shared invocation over active owned keys

Let $\sigma = (\pi, r, c)$ be a service signature and $\Delta$ an ownership context. The invocation
priority condition holds when $\pi$ is strictly less than the rank of every capability $d$ of
$\Delta$ whose protocol does not have head $\mathrm{end}$.
