# Greedy online matching is `1/2`-competitive

Every matching has at most twice as many
edges as the greedy one. An edge of the matching whose right vertex the greedy algorithm matched
is charged to that right vertex, any other edge to its left vertex, which the greedy algorithm
matched by maximality; a matching charges each greedy edge at most once on each side.
