# Greedy assignment on a tree CSP

Let a binary constraint problem have symmetric constraints whose arcs all join a variable and its parent in a forest, and let the variables be listed root first. Suppose the domains are directionally arc consistent (every parent-to-child arc is consistent) and $\mathrm{sel}$ picks an element from every nonempty set. Then the greedy procedure, which assigns the variables in that order, each with a selected value from its domain compatible with its parent's value, succeeds if and only if every domain is nonempty.
