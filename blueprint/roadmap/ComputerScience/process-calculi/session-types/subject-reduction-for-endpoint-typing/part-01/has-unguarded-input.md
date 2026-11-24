# Unguarded input in a process

A process has an unguarded input if it is an input $a(\cdot).p$, or a parallel composition $p \mid
q$ or a choice $p + q$ one of whose components has one, or a restriction $\nu\,p$ or replication
$!p$ whose body has one. $\mathbf{0}$ and outputs have none (continuations of prefixes are not
inspected).
