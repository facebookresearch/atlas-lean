# Satisfying path of a binary decision diagram

The satisfying path of a diagram is found
by a depth-first search for a leaf $\mathrm{true}$ that tries the $\mathrm{hi}$ (true) child of
each node before its $\mathrm{lo}$ (false) child. It is returned as the list of pairs $(v, c)$ of
the variables $v$ tested along the path with the branches $c$ taken (empty at a leaf
$\mathrm{true}$), and the search returns nothing when the diagram has no leaf $\mathrm{true}$.
