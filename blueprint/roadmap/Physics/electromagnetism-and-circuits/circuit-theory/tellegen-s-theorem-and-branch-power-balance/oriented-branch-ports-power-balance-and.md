# Power balance of oriented branch ports and branch reversal

Let `V` be a finite set of nodes and `E` a finite set of branches, each branch `e` with a tail node
`tail(e)` and a head node `head(e)`, and let `A` be the
[electrical incidence matrix](../../../../GraphTheory/algebraic-graph-theory/part-01/oriented-incidence-matrices/oriented-incidence.md). Let `φ` and `j` be real node potentials and
node injections, and `v` and `i` real branch voltages and currents, with current balance `A i = j`
and potential-defined voltages `v = Aᵀ φ`. Then:

- the total branch power equals the total node power, `∑ₑ v(e) i(e) = ∑ₙ φ(n) j(n)`;
- for every branch `e₀`, the network with `e₀` reversed (tail and head of `e₀` swapped,
  incidence `A'`) and the current of `e₀` negated still balances the same injections,
  `A' i' = j`;
- its potential-defined voltages are `v` with the voltage of `e₀` negated, `A'ᵀ φ = v'`.

The first item is [Tellegen's theorem](branch-power-eq-node-power.md) for the electrical incidence.
