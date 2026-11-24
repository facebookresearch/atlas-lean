# Binding a fresh pair keeps disjointness from a lifted context

Let $\Delta$, $\Theta$ be ownership contexts with disjoint domains and $c$ a capability. Then
$\nu_c\Delta$ and $\uparrow_0\Theta$ have disjoint domains, where $\uparrow_0$ raises every variable
name index of an endpoint by one and $\nu_c\Delta$ is $\uparrow_0\Delta$ extended by
$\mathrm{v}_0^{+} \mapsto c$ and $\mathrm{v}_0^{-} \mapsto \bar c$.
