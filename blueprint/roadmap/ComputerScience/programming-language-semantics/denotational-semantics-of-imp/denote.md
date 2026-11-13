# Relational denotational semantics of IMP

The denotation of an IMP command is a binary
relation on states, defined by recursion on the command. The command $\mathtt{skip}$ relates
$s$ to $s'$ iff $s' = s$. For a variable identifier $x$ and an arithmetic expression $a$, the
assignment $x := a$ relates $s$ to $s'$ iff $s'$ is $s$ with $x$ updated to the value of $a$
in $s$. The sequence $c_1; c_2$ relates $s$ to $s'$ iff there is a state $m$ such that $c_1$
relates $s$ to $m$ and $c_2$ relates $m$ to $s'$. For a Boolean expression $b$, the conditional
$\mathtt{if}\ b\ \mathtt{then}\ t\ \mathtt{else}\ e$ relates $s$ to $s'$ iff either $b$
evaluates to true in $s$ and $t$ relates $s$ to $s'$, or $b$ evaluates to false in $s$ and $e$
relates $s$ to $s'$. The denotation of $\mathtt{while}\ b\ \mathtt{do}\ c$ is the least fixed
point, for inclusion of relations, of the one-step unfolding functional of a while loop with
guard $b$ and body relation the denotation of $c$.
