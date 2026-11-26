# The effect-handler calculus has the structural properties

The interface
`TypeSafety.StructuralTyping` has one sort of terms, one sort of types and one kind of binder,
while fine-grain call-by-value has two sorts, values and computations, and only value
variables. The packaging into `Val Op ⊕ Comp Op` and `VTy Op ⊕ CTy Op` (`HasT`, `bindT`,
`instT`, `wkT`) exists to meet that single-sorted interface. The value branch carries the
content: binding at a value type `A` adds an innermost variable `x : A`, and instantiating by a
value `v` is the substitution `[v/x]` into a value or a computation, so the substitution field
is `HasVTy.inst` and `HasCTy.inst`. Binding at a computation type binds nothing and
instantiating by a computation is the identity; these branches hold trivially and only make the
operations total. A context `Γ` extends to `Θ ++ Γ` for a block `Θ` of new innermost variables;
for such an extension the shift `(Θ ++ Γ).length - Γ.length` of `wkT` is the length of `Θ`, and
weakening is `HasVTy.weaken` and `HasCTy.weaken`.
