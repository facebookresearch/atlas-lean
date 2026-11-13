# Compilation of commands

The compiled code $C_p(c)$ of an IMP command $c$ at base program
counter $p$ is the list of stack-machine instructions defined by recursion on $c$, where jump
targets are absolute program counters and $\ell$ denotes instruction counts:
$C_p(\mathbf{skip})$ is empty; $C_p(x := a)$ is the code of $a$ followed by the instruction
store $x$; $C_p(c_1; c_2)$ is $C_p(c_1)$ followed by $C_{p + \ell(c_1)}(c_2)$. For the
conditional $\mathbf{if}\ b\ \mathbf{then}\ c_1\ \mathbf{else}\ c_2$, put $q = p + \ell(b) + 1$
and $r = q + \ell(c_1) + 1$; its code is the code of $b$, then jump-if-zero to $r$, then
$C_q(c_1)$, then jump to $r + \ell(c_2)$, then $C_r(c_2)$. For the loop
$\mathbf{while}\ b\ \mathbf{do}\ c_1$, put $q = p + \ell(b) + 1$; its code is the code of $b$,
then jump-if-zero to $q + \ell(c_1) + 1$, then $C_q(c_1)$, then jump to $p$.
