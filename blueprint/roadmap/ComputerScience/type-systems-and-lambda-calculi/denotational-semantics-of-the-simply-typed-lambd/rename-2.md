# Renaming preserves semantic equality

Fix an interpretation $I$ of the base types. If
terms $t$ and $u$ of type $A$ in a context $\Gamma$ are semantically equal in $I$ (they have the
same denotation in every environment), then for every type-preserving renaming $\rho$ of the
variables of $\Gamma$ into a context $\Delta$, the renamed terms $\rho(t)$ and $\rho(u)$ are
semantically equal in $I$.
