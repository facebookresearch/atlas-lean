# Precondition of an annotated command

For an annotated command $C$ and an assertion $Q$
(the postcondition), the precondition $\mathrm{pre}(C, Q)$ is the assertion computed backwards
as follows: $\mathrm{pre}(\mathrm{skip}, Q) = Q$; $\mathrm{pre}(x := a, Q)$ holds in a state $s$
iff $Q$ holds in the state obtained from $s$ by giving $x$ the value of $a$ in $s$;
$\mathrm{pre}(C_1;\,C_2, Q) = \mathrm{pre}(C_1, \mathrm{pre}(C_2, Q))$; the precondition of
$\mathrm{if}\ b\ \mathrm{then}\ C_1\ \mathrm{else}\ C_2$ for $Q$ holds in a state $s$ iff
$\mathrm{pre}(C_1, Q)$ holds in $s$ when $b$ is true in $s$, and $\mathrm{pre}(C_2, Q)$ holds in
$s$ when $b$ is false in $s$; and the precondition of a loop
$\{I\}\ \mathrm{while}\ b\ \mathrm{do}\ C$ is its invariant $I$, whatever $Q$ is.
