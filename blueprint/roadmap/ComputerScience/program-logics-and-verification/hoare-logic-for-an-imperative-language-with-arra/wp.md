# Verification precondition for the imperative language with arrays

For a statement $c$ and a postcondition $Q$, the precondition $\mathrm{pre}(c, Q)$ is the predicate on
states defined by recursion on $c$:

- $\mathrm{pre}(\mathtt{skip}, Q) = Q$;
- $\mathrm{pre}(x := e, Q)(s)$ holds when $Q(s[x \mapsto e(s)])$ holds;
- $\mathrm{pre}(x := a[e], Q)(s)$ holds when $e(s)$ is smaller than the length of $a$ and
  $Q(s[x \mapsto a_{e(s)}])$ holds;
- $\mathrm{pre}(c_1 ; c_2, Q) = \mathrm{pre}(c_1, \mathrm{pre}(c_2, Q))$;
- $\mathrm{pre}(\mathtt{if}\ b\ \mathtt{then}\ c_1\ \mathtt{else}\ c_2, Q)(s)$ holds when $b(s)$
  implies $\mathrm{pre}(c_1, Q)(s)$ and $\neg b(s)$ implies $\mathrm{pre}(c_2, Q)(s)$;
- for a loop $\mathtt{while}\ b\ \mathtt{do}\ c$ annotated with the invariant $I$,
  $\mathrm{pre}(\mathtt{while}\ b\ \mathtt{do}\ c, Q)(s)$ holds when $I(s)$ holds, every state $s'$
  with $I(s')$ and $\neg b(s')$ satisfies $Q$, and every state $s'$ with $I(s')$ and $b(s')$
  satisfies $\mathrm{pre}(c, I)$.

It is sound for partial correctness: if $\mathrm{pre}(c, Q)$ holds at a state $s$ and $c$ runs from
$s$ to a state $s'$, then $Q$ holds at $s'$. It need not be the weakest such precondition, since for
a loop it requires the annotated invariant. Unlike [the weakest precondition of IMP](../hoare-logic/wp.md),
which is defined from the semantics for total correctness, it is computed from the syntax and the loop
invariants.
