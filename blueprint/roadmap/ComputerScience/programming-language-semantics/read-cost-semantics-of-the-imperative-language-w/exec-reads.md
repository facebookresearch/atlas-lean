# Interpreter counting array reads in the imperative language with arrays

The read-counting interpreter takes a fuel $f$, a statement $c$ and a state $s$ and returns a pair: an outcome (a final state, or failure) and a cost in $\mathbb{N}$. Costs add along the executed computation, and the cost of a computation is kept when a later step fails. With fuel $0$ it returns failure at cost $0$. With fuel $f + 1$ it proceeds by cases on $c$:

- $\mathtt{skip}$ returns $s$ and $x := e$ returns $s[x \mapsto e(s)]$, both at cost $0$;
- the read $x := a[e]$ returns $s[x \mapsto a_{e(s)}]$ at cost $1$ if $e(s) < |a|$ (the length of $a$), and fails at cost $0$ otherwise;
- $c_1 ; c_2$ runs $c_1$ from $s$ with fuel $f$; if it fails, the result is failure with the cost of that run; if it returns $u$, the result is the outcome of running $c_2$ from $u$ with fuel $f$, at the sum of the two costs;
- $\mathtt{if}\ b\ \mathtt{then}\ c_1\ \mathtt{else}\ c_2$ returns the result (outcome and cost) of running, with fuel $f$, $c_1$ from $s$ if $b$ is true in $s$ and $c_2$ from $s$ otherwise;
- a loop $\mathtt{while}\ b\ \mathtt{do}\ c$ returns $s$ at cost $0$ if $b$ is false in $s$; otherwise it runs $c$ from $s$ with fuel $f$ and, as for a sequence, continues with the whole loop from the resulting state with fuel $f$, adding the costs, or fails at the cost of the body's run.

So exactly one unit is charged for each successful in-bounds array read; arithmetic, guards, assignments and control flow are free, and an out-of-bounds read or exhausted fuel costs nothing. The loop invariant is never evaluated.
