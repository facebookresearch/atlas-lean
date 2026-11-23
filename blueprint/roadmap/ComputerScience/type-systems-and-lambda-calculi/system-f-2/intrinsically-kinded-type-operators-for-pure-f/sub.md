# Kind-preserving simultaneous type substitutions

For kinding contexts $\Delta$ and $\mathrm{E}$, a kind-preserving substitution $\sigma : \Delta \to
\mathrm{E}$ assigns to every [type variable](kvar.md) of kind $\kappa$ in $\Delta$ a [type
operator](ty.md) $\sigma(\alpha_i) \in \mathrm{Ty}^{\kappa}_{\mathrm{E}}$ of the same kind, for
every kind $\kappa$.
