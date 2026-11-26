# Unwinding for terminating runs of a secure command

Let $c$ be an IMP command that is secure under policy $\Gamma$ at some program-counter level $pc$. If $c$ terminates from store $s$ in store $s'$ and from store $t$ in store $t'$ (big-step semantics), and $s$ and $t$ are low-equivalent, then $s'$ and $t'$ are low-equivalent.
