# Termination-insensitive noninterference

Let $c$ be an IMP command that is secure under a security policy $\Gamma$ in a low program-counter context. If stores $s$ and $t$ agree on all low variables of $\Gamma$, and $c$ terminates from $s$ in $s'$ and from $t$ in $t'$, then $s'$ and $t'$ agree on all low variables.
