# Fourier Mukai Comp Iso Of Comparisons

Assemble the seven-step comparison proof from public AxiomMath/Stacks
`FourierMukai/Composition.lean`.

The supplied natural isomorphisms are the derived base-change comparison,
monoidality of derived pullback, the two projection-formula comparisons,
tensor associativity, and the pullback/pushforward composition comparisons.
Base change and the projection formulas are supplied only on their actual
quasi-coherent input subcategories. The three preservation hypotheses allow
the preceding functors to enter those subcategories.

This is a complete conditional construction. It asserts neither existence
nor invertibility of any geometric comparison. In the flat, quasi-compact,
quasi-separated setting those must be established separately using Stacks
08IB, 08EU and the quasi-coherent preservation results.
