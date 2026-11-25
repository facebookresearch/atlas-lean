# Call-by-name big-step evaluation

Call-by-name big-step evaluation $M \Downarrow_n V$
of the simply typed $\lambda$-calculus relates two terms of the same type in the same context
$\Gamma$. It is the least relation closed under two rules: every abstraction $\lambda x.\,N$
evaluates to itself, and if $f \Downarrow_n \lambda x.\,N$ and $N[a/x] \Downarrow_n v$, then
$f\,a \Downarrow_n v$. The argument $a$ is substituted for $x$ without being evaluated.
