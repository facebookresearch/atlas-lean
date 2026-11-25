# Rosati Compatible

Rosati compatibility of `L` with a family `act : I → (A ⟶ A)` of
endomorphisms of `A` over the base (`act_over`) and a map `star : I → I`:
for every `b : I`, the pullback of the Mumford bundle along
`rosatiLiftLeft`, `(x, y) ↦ (x, act b y)`, and its pullback along
`rosatiLiftRight`, `(x, y) ↦ (act (star b) x, y)`, are locally isomorphic
over the base `Spec S`.  Nothing else is asked of the inputs: `I` carries no
structure, the maps `act b` need not form an action or respect the group
law, and `star` need not be an involution (a constant map on a two-element
type is allowed).  The name refers to the use with `act` an action of a ring
on `A` and `star` an involution of that ring.
