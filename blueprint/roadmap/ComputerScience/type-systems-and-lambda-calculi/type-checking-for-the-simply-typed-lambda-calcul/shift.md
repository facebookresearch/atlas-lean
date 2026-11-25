# Shifting raw terms

For natural numbers $k$ (the amount) and $c$ (the cutoff, $0$ by
default), shifting a raw term by $k$ at cutoff $c$ replaces a variable index $n$ by $n + k$ if
$c \le n$ and leaves it unchanged otherwise, shifts both sides of an application by $k$ at
cutoff $c$, and sends $\lambda A.\,t$ to $\lambda A.\,t'$, where $t'$ is $t$ shifted by $k$ at
cutoff $c + 1$.
