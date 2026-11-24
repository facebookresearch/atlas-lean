# Verification condition of an annotated command

For an annotated command $C$ and an
assertion $Q$ (the postcondition), the verification condition $\mathrm{vc}(C, Q)$ is the
proposition defined as follows, where $\mathrm{pre}$ is the precondition of an annotated
command: $\mathrm{vc}(\mathrm{skip}, Q)$ and $\mathrm{vc}(x := a, Q)$ are true;
$\mathrm{vc}(C_1;\,C_2, Q)$ holds iff $\mathrm{vc}(C_1, \mathrm{pre}(C_2, Q))$ and
$\mathrm{vc}(C_2, Q)$ hold; the verification condition of
$\mathrm{if}\ b\ \mathrm{then}\ C_1\ \mathrm{else}\ C_2$ for $Q$ holds iff $\mathrm{vc}(C_1, Q)$
and $\mathrm{vc}(C_2, Q)$ hold; and for a loop $\{I\}\ \mathrm{while}\ b\ \mathrm{do}\ C'$, the
verification condition for $Q$ holds iff every state satisfying $I$ in which $b$ is true
satisfies $\mathrm{pre}(C', I)$, every state satisfying $I$ in which $b$ is false satisfies
$Q$, and $\mathrm{vc}(C', I)$ holds.
