# The call-by-name CPS translation of a renaming

Fix an answer type $R$. The translation
of a context $\Gamma$ replaces each type $A$ in it by the computation type $(A^* \to R) \to R$,
where $A^*$ is the call-by-name translation of $A$, and a variable $x$ of $\Gamma$ becomes the
variable $\overline{x}$ at the same position of the translated context. A renaming $\rho$ from
$\Gamma$ to $\Delta$, a type-preserving map from the variables of $\Gamma$ to those of $\Delta$,
is transported to the renaming $\overline{\rho}$ of the translated contexts with
$\overline{\rho}(\overline{x}) = \overline{\rho(x)}$ for every variable $x$ of $\Gamma$.
