# Small-step call-by-value reduction in STLC

One-step reduction on terms of type $A$ in a
context $\Gamma$ is the least relation closed under three left-to-right call-by-value rules: if
$f$ reduces to $f'$, then the application $f\,a$ reduces to $f'\,a$; if $f$ is a value and $a$
reduces to $a'$, then $f\,a$ reduces to $f\,a'$; and if $a$ is a value, then the application of
the abstraction of $b$ to $a$ reduces to $b[a]$, the result of substituting $a$ for the newest
free variable of $b$.
