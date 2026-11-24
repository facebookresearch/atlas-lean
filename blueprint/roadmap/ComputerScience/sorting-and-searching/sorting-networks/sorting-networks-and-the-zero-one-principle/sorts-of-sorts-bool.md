# The 0-1 principle

Let $n$ be a natural number and let $C$ be a comparator network on $n$ wires that sorts every
Boolean input: for every assignment of a value in $\{\mathrm{false}, \mathrm{true}\}$ to each wire,
ordered by $\mathrm{false} < \mathrm{true}$, the output of $C$ is monotone in the wire order. Then
for every linearly ordered type $\alpha$, the network $C$ sorts every input over $\alpha$: for
every assignment $v$ of a value in $\alpha$ to each wire, the output of $C$ on $v$ is monotone in
the wire order (CLRS Theorem 27.2).
