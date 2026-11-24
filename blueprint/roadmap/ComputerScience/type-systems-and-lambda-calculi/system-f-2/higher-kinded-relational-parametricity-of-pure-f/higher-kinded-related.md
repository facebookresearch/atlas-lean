# Higher-kinded identity inhabitants preserve admissible relations

Let $\Delta$ be a kinding context and $t \in \mathrm{Tm}_{\Delta,0}$ with $\emptyset \vdash t :
\forall_{\star \Rightarrow \star}\,\forall_\star\,(\alpha_1\,\alpha_0 \to \alpha_1\,\alpha_0)$
([typing](../pure-f-typing-with-proved-type-beta-conversion/typing.md)). Let $F, G \in
\mathrm{Ty}^{\star \Rightarrow \star}_{\Delta}$ and $A, B \in \mathrm{Ty}^{\star}_{\Delta}$ be
arbitrary, $\Phi$ any function from [β-invariant
relations](../../system-f/binary-beta-invariant-relations/rel.md) to β-invariant relations, $R$ a
β-invariant relation, and $x$, $y$ model terms with $\Phi(R)(x, y)$. Then $\Phi(R)(e\,x, e'\,y)$,
where $e$ and $e'$ are the
[erasures](../f-closing-instances-in-the-single-existing-term/erase-model.md) of $t\,[F]\,[A]$ and
$t\,[G]\,[B]$ to the untyped term model.
