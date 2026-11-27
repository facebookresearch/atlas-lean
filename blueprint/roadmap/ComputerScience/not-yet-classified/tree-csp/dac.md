# Directional arc consistency pass

For a tree-structured constraint problem with parent map and variable order, the pass processes the variables in reverse order; at a variable $x$ with parent $p$ it revises the domain of $p$ against $x$, removing values of $p$ without support in the domain of $x$, and leaves the domains unchanged at a variable without parent. The result is returned with its constraint-check cost.
