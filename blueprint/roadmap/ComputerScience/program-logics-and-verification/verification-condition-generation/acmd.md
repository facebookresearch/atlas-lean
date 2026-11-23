# Annotated commands

An annotated command is built like an IMP command, from skip,
assignments $x := a$ of an arithmetic expression $a$ to a variable $x$ (a natural number),
sequential composition $C_1;\,C_2$ and conditionals
$\mathrm{if}\ b\ \mathrm{then}\ C_1\ \mathrm{else}\ C_2$ on a boolean expression $b$, except that
every while loop $\{I\}\ \mathrm{while}\ b\ \mathrm{do}\ C$ also carries an assertion $I$, its
invariant.
