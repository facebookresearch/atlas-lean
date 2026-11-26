# Big-step call-by-name evaluation of PCF

Write $\underline{n}$ for the numeral
$\mathsf{succ}^n\,\mathsf{zero}$. For closed PCF terms $t$ and $v$ of the same type,
$t \Downarrow v$ ($t$ evaluates to $v$) is the least relation closed under the following rules,
where all terms are closed and $n$ ranges over natural numbers.
Every $\lambda$-abstraction evaluates to itself, and $\mathsf{zero} \Downarrow \mathsf{zero}$.
If $t \Downarrow \underline{n}$, then $\mathsf{succ}\,t \Downarrow \underline{n+1}$.
If $t \Downarrow \mathsf{zero}$, then $\mathsf{pred}\,t \Downarrow \mathsf{zero}$; if
$t \Downarrow \underline{n+1}$, then $\mathsf{pred}\,t \Downarrow \underline{n}$.
For the zero test, if $t \Downarrow \mathsf{zero}$ and $s_1 \Downarrow v$, then
$\mathsf{ifz}\,t\,s_1\,s_2 \Downarrow v$; if $t \Downarrow \underline{n+1}$ and $s_2 \Downarrow v$,
then $\mathsf{ifz}\,t\,s_1\,s_2 \Downarrow v$. If $f \Downarrow \lambda x.\,b$ and
$b[a/x] \Downarrow v$, then $f\,a \Downarrow v$, where $b[a/x]$ substitutes the unevaluated
argument $a$ for $x$ in $b$. If $t\,(\mathsf{fix}\,t) \Downarrow v$, then
$\mathsf{fix}\,t \Downarrow v$.
