# Simultaneous type substitution in System F types

For a type substitution $\sigma$ assigning to each $i < n$ a type $\sigma(i) \in \mathrm{Ty}_k$, the substitution $A[\sigma] \in \mathrm{Ty}_k$ of a [type](ty.md) $A \in \mathrm{Ty}_n$ is defined by $\alpha_i[\sigma] = \sigma(i)$, $(A \to B)[\sigma] = A[\sigma] \to B[\sigma]$ and $(\forall B)[\sigma] = \forall\,(B[\sigma^{\uparrow}])$, with the [lifted substitution](lift-sub.md) under the binder; it avoids capture.
