# Backtracking search with forward checking

The search takes fuel $n$, current domains, a partial assignment and the set $U$ of unassigned variables, and returns a total assignment or nothing:

- with fuel $0$, or with $U$ empty, it returns the total assignment read off the partial assignment if every variable is assigned, and nothing otherwise;
- otherwise it picks a variable $x \in U$ by the search order and tries the values of $x$ in the order the search order gives. A value $a$ is admitted when it is compatible with itself on the arcs of $x$ and, after forward checking (removing from each other domain the values incompatible with $x = a$), every other variable of $U$ still has a nonempty domain. For an admitted value it recurses with fuel $n - 1$, the narrowed domains, $x$ assigned to $a$ and $x$ removed from $U$;
- it returns the first success of these recursive calls, and nothing if every value fails.
