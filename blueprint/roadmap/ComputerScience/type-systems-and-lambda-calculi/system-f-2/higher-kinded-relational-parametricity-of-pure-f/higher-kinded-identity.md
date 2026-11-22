# Closed inhabitants of the higher-kinded identity type are identities

Let $\Delta$ be a kinding context and $t \in \mathrm{Tm}_{\Delta,0}$ a term with $\emptyset \vdash t
: \forall_{\star \Rightarrow \star}\,\forall_\star\,(\alpha_1\,\alpha_0 \to \alpha_1\,\alpha_0)$ in
the empty term context ([typing](../pure-f-typing-with-proved-type-beta-conversion/typing.md)). Then
for every $F \in \mathrm{Ty}^{\star \Rightarrow \star}_{\Delta}$, $A \in
\mathrm{Ty}^{\star}_{\Delta}$ and every term $x$ of the untyped term model, $e\,x =_\beta x$, where
$e$ is the [erasure](../f-closing-instances-in-the-single-existing-term/erase-model.md) of
$t\,[F]\,[A]$ to the untyped term model.
