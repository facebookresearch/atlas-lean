# Lifting a type substitution under a type binder

For a [kind-preserving substitution](sub.md) $\sigma : \Delta \to \mathrm{E}$ and a kind $\mu$, the
lifted substitution $\sigma^{\uparrow} : \mu \cdot \Delta \to \mu \cdot \mathrm{E}$ sends $\alpha_0$
to $\alpha_0$ and $\alpha_{i+1}$ to $\sigma(\alpha_i)$ [renamed](rename.md) by the successor
renaming $\alpha_j \mapsto \alpha_{j+1}$, so that old images are not captured by the new binder.
