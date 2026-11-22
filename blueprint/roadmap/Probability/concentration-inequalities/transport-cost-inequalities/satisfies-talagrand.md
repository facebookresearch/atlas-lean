# Talagrand's quadratic transport-cost inequality

A probability measure $m$ on a metric space with a σ-algebra satisfies Talagrand's inequality with
constant $C \in \mathbb{R}$ if

$$W_2(\mu, m)^2 \le C^+ \operatorname{KL}(\mu \,\|\, m)$$

for every probability measure $\mu$, both sides taken in $[0, \infty]$ with $C^+ = \max(C, 0)$, where
$W_2$ is the [quadratic Wasserstein distance](../../../MeasureTheory/optimal-transport/wasserstein-distances/wasserstein-distance/wasserstein.md).
For $C \ge 0$ this is the usual inequality $W_2(\mu, m)^2 \le C \operatorname{KL}(\mu \,\|\, m)$.
In Villani's notation $T_2(\lambda)$ is the case $C = 2/\lambda$; the standard Gaussian satisfies
it with $C = 2$ ([Talagrand's transport inequality for the Gaussian measure](../talagrand-std-gaussian.md)).

## Sources

- N. Gigli, M. Ledoux, *From log Sobolev to Talagrand: a quick proof*, Discrete Contin. Dyn. Syst. Ser. A (2013); preprint at https://cvgmt.sns.it/paper/1689/, inequality (2.3).
