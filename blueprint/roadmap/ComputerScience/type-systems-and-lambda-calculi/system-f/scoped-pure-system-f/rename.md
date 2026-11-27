# Type-variable renaming in System F types

For a renaming $\rho : \{0, \dots, n - 1\} \to \{0, \dots, k - 1\}$, the renaming $A\langle\rho\rangle \in \mathrm{Ty}_k$ of a [type](ty.md) $A \in \mathrm{Ty}_n$ is defined by $\alpha_i\langle\rho\rangle = \alpha_{\rho(i)}$, $(A \to B)\langle\rho\rangle = A\langle\rho\rangle \to B\langle\rho\rangle$ and $(\forall B)\langle\rho\rangle = \forall\,(B\langle\rho^{\uparrow}\rangle)$, with the [lifted renaming](lift-ren.md) under the binder; it avoids capture.
