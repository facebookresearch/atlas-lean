# Kinded type variables of Fω

A kinding context is a finite list $\Delta = \kappa_0 \cdot \kappa_1 \cdots \kappa_{n-1}$ of
[kinds](kind.md), whose head $\kappa_0$ is the kind of the most recently bound type variable. For a
kinding context $\Delta$ and a kind $\kappa$, the type variables of kind $\kappa$ in $\Delta$ are
the de Bruijn indices $\alpha_i$ with $i < n$ and $\kappa_i = \kappa$. Inductively: $\alpha_0$ is a
variable of kind $\kappa$ in $\kappa \cdot \Delta$, and if $\alpha_i$ is a variable of kind $\kappa$
in $\Delta$ then $\alpha_{i+1}$ is a variable of kind $\kappa$ in $\mu \cdot \Delta$ for every kind
$\mu$.
