# The shift of a Büchi automaton

Let $A$ be a Büchi automaton over the alphabet of sets of
atoms. Its shift is the Büchi automaton whose states are the states of $A$ together with one new
state $\bot$, whose only start state is $\bot$, and whose accepting states are the accepting states
of $A$. Its transitions are exactly the following: on every letter, from $\bot$ to each start state
of $A$; and on a letter $x$, from a state $q$ of $A$ to a state $q'$ of $A$ whenever $A$ has a
transition from $q$ to $q'$ on $x$.

The shift accepts a word exactly when $A$ accepts the word with its first letter removed.
