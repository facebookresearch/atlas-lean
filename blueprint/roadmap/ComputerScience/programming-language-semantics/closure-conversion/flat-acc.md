# Accessors inside flat code

For a list $L$ of natural numbers, the flat accessors for $L$
assign a target term to each variable: variable $0$ is sent to $\mathsf{fst}\,\#0$, and variable
$j + 1$ is sent to $\mathsf{fst}\,(\mathsf{snd}^k\,(\mathsf{snd}\,\#0))$. Here $\#0$ is target
variable $0$, $\mathsf{snd}^k$ applies the second projection $k$ times, and $k$ is the index of the
first occurrence of $j$ in $L$, or the length of $L$ if $j$ does not occur in $L$.

Inside flat code the parameter $\#0$ is the pair of the argument and the environment, so variable
$0$ is the argument and variable $j + 1$ is the entry of the environment at the position of $j$
in $L$.
