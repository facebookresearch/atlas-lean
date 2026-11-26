# The tree-CSP algorithm returns only solutions

Let $P$ be a symmetric binary constraint problem whose arcs all join a variable and its parent, for
a parent map with a rooted order listing every variable once, root first. For every selection
function and all domains, any assignment returned by the tree-CSP algorithm (a directional arc
consistency pass followed by greedy assignment) is a solution.
