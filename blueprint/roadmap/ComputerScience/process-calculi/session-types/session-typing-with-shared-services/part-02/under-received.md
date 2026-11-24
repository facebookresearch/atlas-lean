# Nonaliasing survives adding a received parameter under a binder

Let $\Gamma$ be a service environment, $\Delta$ an ownership context, $f$ a map from names to names
that does not alias $\Delta$ with $\Gamma$, $r$ a polarity and $c$ a capability. Then $f^{\uparrow}$
does not alias $(\uparrow_0\Delta)[\mathrm{v}_0^{r} \mapsto c]$ with $\Gamma$ ($f^{\uparrow}$ fixes
$\mathrm{v}_0$, which is not a constant).
