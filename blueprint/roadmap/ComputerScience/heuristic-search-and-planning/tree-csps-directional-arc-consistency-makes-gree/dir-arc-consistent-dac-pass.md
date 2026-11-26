# Dir Arc Consistent dac Pass

Let the parent map have no variable as its own parent, and let $ys$ be a list of variables still to process, which need not enumerate all variables, such that no earlier listed variable is the parent of a later one, every parent of a listed variable is listed, and every arc from a parent into an unlisted child is already consistent in the current domains. Then, in the domains returned by the directional arc consistency pass over $ys$, every parent-to-child arc is consistent.
