# Statements of the imperative language with arrays

The statements of the imperative language with arrays are built inductively from the following constructors:

- $\mathtt{skip}$;
- the assignment $x := e$ of an arithmetic expression $e$ to a variable $x$ (variables are strings);
- the read $x := a[e]$, which stores in $x$ the entry at index $e$ of an array $a$ of natural numbers that is part of the statement itself;
- the sequence $c_1 ; c_2$;
- the conditional $\mathtt{if}\ b\ \mathtt{then}\ c_1\ \mathtt{else}\ c_2$ for a Boolean expression $b$;
- the loop $\mathtt{while}\ b\ \mathtt{do}\ c$, which also carries an invariant $I$, an arbitrary predicate on states.

Arrays are immutable: no statement changes them, and they are not part of the state. The loop invariant is ghost data used for verification conditions; neither the big-step semantics nor the interpreter evaluates it.
