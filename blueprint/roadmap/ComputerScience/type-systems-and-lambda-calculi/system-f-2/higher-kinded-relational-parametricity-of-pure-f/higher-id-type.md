# Higher-kinded identity type

For every kinding context $\Delta$, the higher-kinded identity type is $\forall_{\star \Rightarrow
\star}\,\forall_\star\,(\alpha_1\,\alpha_0 \to \alpha_1\,\alpha_0) \in \mathrm{Ty}^{\star}_{\Delta}$
([type operators](../intrinsically-kinded-type-operators-for-pure-f/ty.md)): for every operator
$\alpha_1$ of kind $\star \Rightarrow \star$ and every type $\alpha_0$, a function from
$\alpha_1\,\alpha_0$ to itself.
