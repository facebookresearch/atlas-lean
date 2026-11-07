# Big-step semantics of IMP

The big-step relation says when running a command $c$ from a
state $s$ terminates in a state $t$; we then say that $c$ takes $s$ to $t$. It is the least
relation satisfying the following rules. The command $\mathtt{skip}$ takes $s$ to $s$. The
assignment $x := a$ takes $s$ to the state $s[x \mapsto a(s)]$, which agrees with $s$ except that
$x$ has the value $a(s)$ of the arithmetic expression $a$ in $s$. If $c_1$ takes $s$ to $u$ and
$c_2$ takes $u$ to $t$, then the sequence $c_1 ; c_2$ takes $s$ to $t$. If the Boolean expression
$b$ is true in $s$ and $c_1$ takes $s$ to $t$, then
$\mathtt{if}\ b\ \mathtt{then}\ c_1\ \mathtt{else}\ c_2$ takes $s$ to $t$; if $b$ is false in $s$
and $c_2$ takes $s$ to $t$, then it also takes $s$ to $t$. If $b$ is false in $s$, then the loop
$\mathtt{while}\ b\ \mathtt{do}\ c$ takes $s$ to $s$; if $b$ is true in $s$, $c$ takes $s$ to $u$
and the loop takes $u$ to $t$, then the loop takes $s$ to $t$.
