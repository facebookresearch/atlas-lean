# Heap commands

Heap commands extend the commands of IMP with heap operations. A heap
command is one of: $\mathbf{skip}$; an assignment $x := a$; a sequence $c_1; c_2$; a
conditional $\mathbf{if}\ b\ \mathbf{then}\ c_1\ \mathbf{else}\ c_2$; a loop
$\mathbf{while}\ b\ \mathbf{do}\ c$; a heap read $x := [a]$; a heap write $[a] := e$; an
allocation $x := \mathbf{alloc}(e)$; or a deallocation $\mathbf{free}(a)$. Here $x$ is a variable
(a natural number), $a$ and $e$ are arithmetic expressions, $b$ is a Boolean expression, and $c$,
$c_1$, $c_2$ are heap commands.
