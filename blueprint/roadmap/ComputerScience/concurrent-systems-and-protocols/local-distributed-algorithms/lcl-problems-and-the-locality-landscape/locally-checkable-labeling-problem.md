# Locally checkable labeling problem

Fix integers $\Delta, r \ge 1$ and finite sets $\Sigma_{\mathrm{in}}, \Sigma_{\mathrm{out}}$. A locally checkable labeling (LCL) problem $\Pi$ on graphs of maximum degree at most $\Delta$ is specified by a finite set $\mathcal{C}$ of allowed centred configurations: isomorphism classes of graphs of radius at most $r$ around a distinguished centre, with maximum degree $\Delta$, whose vertices carry input labels from $\Sigma_{\mathrm{in}}$ and output labels from $\Sigma_{\mathrm{out}}$. An output labeling $\lambda : V \to \Sigma_{\mathrm{out}}$ of an input-labelled graph $G$ is a solution if for every vertex $v$ the radius-$r$ neighbourhood of $v$, centred at $v$ and with its labels, belongs to $\mathcal{C}$. Examples include proper $k$-colouring, maximal independent set, maximal matching (with edge labels encoded at endpoints) and sinkless orientation.

## Depends on

- [The LOCAL model](../../distributed-execution-models/the-local-model.md)

## Sources

- M. Naor, L. Stockmeyer, "What Can Be Computed Locally?", SIAM Journal on Computing 24(6) (1995); STOC 1993.
