# Nonaliasing survives binding a private session pair

Let $\Gamma$ be a service environment, $\Delta$ an ownership context, $f$ a map from names to names
that does not alias $\Delta$ with $\Gamma$, and $c$ a capability. Then $f^{\uparrow}$ does not alias
$\nu_c\Delta$ with $\Gamma$, where $\nu_c\Delta$ is $\uparrow_0\Delta$ extended by $\mathrm{v}_0^{+}
\mapsto c$ and $\mathrm{v}_0^{-} \mapsto \bar c$.
