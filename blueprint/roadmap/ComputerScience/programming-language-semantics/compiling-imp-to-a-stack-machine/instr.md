# Stack machine instructions

An instruction of the stack machine is one of
$\mathsf{push}\ n$, $\mathsf{load}\ x$ and $\mathsf{store}\ x$ for natural numbers $n$ and $x$;
the arithmetic instructions $\mathsf{add}$, $\mathsf{sub}$ and $\mathsf{mul}$; the comparison and
Boolean instructions $\mathsf{eq}$, $\mathsf{le}$, $\mathsf{not}$ and $\mathsf{and}$; and the
jumps $\mathsf{jump}\ t$ and $\mathsf{jumpIfZero}\ t$ for a natural number $t$. Jump targets are
absolute program counters.
