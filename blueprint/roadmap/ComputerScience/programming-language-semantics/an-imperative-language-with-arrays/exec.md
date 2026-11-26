# Fuel-bounded interpreter for the imperative language with arrays

For a fuel $f \in \mathbb{N}$, a statement $c$ and a state $s$, the interpreter either returns a final state or fails. Write $|a|$ for the length of an array $a$. With fuel $0$ it fails. With fuel $f + 1$ it proceeds by cases on $c$:

- $\mathtt{skip}$ returns $s$, and $x := e$ returns $s[x \mapsto e(s)]$;
- the read $x := a[e]$ returns $s[x \mapsto a_{e(s)}]$ if $e(s) < |a|$, and fails otherwise;
- $c_1 ; c_2$ runs $c_1$ from $s$ with fuel $f$ and, if that returns a state $u$, runs $c_2$ from $u$ with fuel $f$; it fails if either run fails;
- $\mathtt{if}\ b\ \mathtt{then}\ c_1\ \mathtt{else}\ c_2$ runs $c_1$ from $s$ with fuel $f$ if $b$ is true in $s$, and $c_2$ from $s$ with fuel $f$ otherwise;
- a loop $\mathtt{while}\ b\ \mathtt{do}\ c$ returns $s$ if $b$ is false in $s$; otherwise it runs $c$ from $s$ with fuel $f$ and, if that returns $u$, runs the whole loop from $u$ with fuel $f$, failing if either run fails.

The fuel bounds the depth of recursion, not the number of executed statements. Failure means exhausted fuel or an out-of-bounds read. The loop invariant is never evaluated.
