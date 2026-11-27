# Ranked typing is invariant under scope extrusion

For every natural number $n$, ownership context $\Delta$ and processes $p$, $q$,

$$
\Delta \vdash^{\mathrm{rk}}_n (\nu\,p) \mid q \iff \Delta \vdash^{\mathrm{rk}}_n \nu\,(p \mid \uparrow_0 q),
$$

where $\uparrow_0 q$ adds one to every free variable index of $q$.
