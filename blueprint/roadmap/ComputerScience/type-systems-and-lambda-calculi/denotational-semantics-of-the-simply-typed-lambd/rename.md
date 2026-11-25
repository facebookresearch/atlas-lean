# Renaming an environment

Given a renaming $\rho$ from context $\Gamma$ to context
$\Delta$ (a type-preserving map from the variables of $\Gamma$ to those of $\Delta$) and an
environment $\eta$ for $\Delta$, the renamed environment for $\Gamma$ sends each variable $x$ of
$\Gamma$ to $\eta(\rho(x))$; that is, it is the composite $\eta \circ \rho$.
