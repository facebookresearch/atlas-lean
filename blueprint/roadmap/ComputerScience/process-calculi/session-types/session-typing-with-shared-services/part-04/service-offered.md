# Typed replicated shared inputs are offered services

Let $n$, $s$ be natural numbers, $\Gamma$ a service environment, $\Delta$ an ownership context and
$p$ a process with $\Gamma; \Delta \vdash_n {!\mathrm{c}_s(\cdot).p}$. Then there is a service
signature $\sigma$ such that ${!\mathrm{c}_s(\cdot).p}$ offers $s$ with signature $\sigma$:
$\Gamma(s) = \sigma$ and the process contains a replication whose body has an unguarded input on
$\mathrm{c}_s$.
