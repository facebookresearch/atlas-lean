# DC economic dispatch as a linear program

## The DC dispatch problem

- [Generator-to-bus incidence matrix](generator-incidence.md)
- [Branch-flow coefficient matrix of the DC model](branch-flow-matrix.md)
- [Feasible DC dispatch](is-dispatch-feasible.md)
- [Linear cost of a dispatch](dispatch-cost.md)

## The linear program encoding

- [Number of variables of the dispatch linear program](num-vars.md)
- [Number of constraints of the dispatch linear program](num-rows.md)
- [Constraint rows on the free variables](free-rows.md)
- [Row selecting the reference angle](reference-row.md)
- [Constraint matrix on generation and angles](free-constraint-matrix.md)
- [Constraint matrix of the dispatch linear program](lp-matrix.md)
- [Right-hand side of the dispatch linear program](lp-rhs.md)
- [Objective of the dispatch linear program](lp-objective.md)
- [Free variables recovered from an LP point](free-part.md)
- [Generation decoded from an LP point](decode-generation.md)
- [Angles decoded from an LP point](decode-angle.md)
- [LP point encoding a dispatch](encode.md)

## Generation, flows and nodal balance

- [Generation collected at each bus](generator-incidence-mul-vec-apply.md)
- [The branch-flow matrix gives the DC branch flows](branch-flow-matrix-mul-vec.md)
- [Nodal balance equals the DC injection balance](balance-iff-dc-injection.md)

## Encoding and decoding

- [Encoded LP points are nonnegative](encode-nonneg.md)
- [Decoding an encoded dispatch returns its generation](decode-generation-encode.md)
- [Decoding an encoded dispatch returns its angles](decode-angle-encode.md)
- [The LP matrix acts through the free part](lp-matrix-mul-vec.md)
- [The LP objective is minus the cost of the decoded generation](lp-objective-dot-product.md)
- [The LP objective of an encoded dispatch is minus its cost](lp-objective-encode.md)

## Feasibility in both directions

- [Feasible dispatches encode to feasible LP points](encode-feasible.md)
- [Feasible LP points decode to feasible dispatches](decode-feasible.md)
- [A dispatch is feasible iff a feasible LP point decodes to it](dispatch-feasible-iff-exists-lp.md)
- [The dispatch problem is feasible iff its linear program is](dispatch-nonempty-iff-lp-nonempty.md)

## Optimality transfer

- [A decoded optimal LP point costs no more than any feasible dispatch](decode-optimal.md)
- [A minimum-cost dispatch encodes to an optimal LP point](encode-optimal.md)

## Correspondence of the two problems

- [The DC dispatch problem and its linear program correspond](dispatch-encoding-correct.md)
