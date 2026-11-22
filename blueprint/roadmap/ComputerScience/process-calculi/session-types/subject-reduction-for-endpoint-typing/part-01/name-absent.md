# Absence of a physical name from a process

Absence of a name $a$ from a process is defined by recursion on the process: $a$ is absent from
$\mathbf{0}$; from $\overline{b}\langle c\rangle.p$ if $a \ne b$, $a \ne c$ and $a$ is absent from
$p$; from $b(\cdot).p$ if $a \ne b$ and $\uparrow_0 a$ is absent from $p$; from $p \mid q$ and $p +
q$ if it is absent from both; from $\nu\,p$ if $\uparrow_0 a$ is absent from $p$; and from $!p$ if
it is absent from $p$. Here $\uparrow_0 a$ raises the index of $a$ by one if $a$ is a variable,
tracking the same name under a binder.
