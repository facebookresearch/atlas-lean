# Big-step semantics of the imperative language with arrays

The big-step relation says when running a statement $c$ from a state $s$ ends in a state $t$. It is
the least relation satisfying the following rules. $\mathtt{skip}$ takes $s$ to $s$. The assignment
$x := e$ takes $s$ to $s[x \mapsto e(s)]$, where $e(s)$ is the value of $e$ in $s$. The read
$x := a[e]$ from an immutable array $a$ takes $s$ to $s[x \mapsto a_{e(s)}]$ provided that the index
$e(s)$ is smaller than the length of $a$; out of bounds it has no execution. If $c_1$ takes $s$ to $u$
and $c_2$ takes $u$ to $t$, then $c_1 ; c_2$ takes $s$ to $t$. If $b$ is true in $s$ and $c_1$ takes
$s$ to $t$, then $\mathtt{if}\ b\ \mathtt{then}\ c_1\ \mathtt{else}\ c_2$ takes $s$ to $t$; if $b$ is
false in $s$ and $c_2$ takes $s$ to $t$, then it also takes $s$ to $t$. A loop
$\mathtt{while}\ b\ \mathtt{do}\ c$, annotated with an invariant that the semantics ignores, takes $s$
to $s$ if $b$ is false in $s$, and takes $s$ to $t$ if $b$ is true in $s$, $c$ takes $s$ to $u$ and
the loop takes $u$ to $t$.

These are the rules of [the big-step semantics of IMP](../operational-semantics-of-imp/big-step.md), with the
read statement added.
