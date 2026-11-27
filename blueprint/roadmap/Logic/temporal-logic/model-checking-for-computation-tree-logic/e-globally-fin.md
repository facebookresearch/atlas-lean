# Finite existential-globally set

Let $\mathcal{T}$ be a labelled transition system with
finitely many states and finitely many labels, decidable transitions and decidable equality of
states, and let $A$ be a set of states. For a set $Z$ of states write
$\mathrm{Pre}_\exists(Z)$ for the set of states having a transition into $Z$. The
existential-globally set of $A$ is obtained by applying the map
$Z \mapsto A \cap \mathrm{Pre}_\exists(Z)$ to the set of all states $n$ times, where $n$ is the
number of states.

Since this map is monotone, the iteration has stabilized after $n$ steps and the result is its
greatest fixed point.
