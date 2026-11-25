# Shared invocation and input worker preserve the combined interface

Let $n$, $s$ be natural numbers, $\Gamma$ a service environment with $s$ declared, $\Delta$,
$\Theta$ ownership contexts with disjoint domains, $b$ a name and $p$, $q$ processes. If $\Gamma;
\Delta \vdash_n \overline{\mathrm{c}_s}\langle b\rangle.p$ and $\Gamma; \Theta \vdash_n
\mathrm{c}_s(\cdot).q$, then $\Gamma; \Delta \cup \Theta \vdash_n p \mid q\{b\}$.
