# Typing rule for a replicated input on a shared name

Let $n$, $s$ be natural numbers, $\Gamma$ a service environment with $\Gamma(s) = (\pi, r, c)$,
$\Delta$ an ownership context all of whose capabilities have head $\mathrm{end}$, all of whose
endpoints have names scoped at depth $n$ and which is separated from $\Gamma$, and $p$ a process
with $\Gamma; \{\mathrm{v}_0^{r} \mapsto c\} \vdash_{n+1} p$. Then $\Gamma; \Delta \vdash_n
{!\mathrm{c}_s(\cdot).p}$.
