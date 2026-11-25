# Greedy assignment is sound on a tree-structured CSP

Let a binary constraint satisfaction problem have symmetric constraints, every constraint arc joining a variable and its parent in a forest, a variable order that lists every variable exactly once with each parent before its children and no variable its own parent, and a selector that returns only members and returns a value for every nonempty set. Then any assignment the greedy root-first algorithm returns is a solution.
