# Inversion of runtime typing for a replicated shared input

Let $n$, $s$ be natural numbers, $\Gamma$ a service environment, $\Delta$ an ownership context and
$p$ a process with $\Gamma; \Delta \vdash_n {!\mathrm{c}_s(\cdot).p}$. Then there is a service
signature $\sigma = (\pi, r, c)$ with $\Gamma(s) = \sigma$ such that every capability of $\Delta$
has head $\mathrm{end}$ and $\Gamma; \{\mathrm{v}_0^{r} \mapsto c\} \vdash_{n+1} p$.
