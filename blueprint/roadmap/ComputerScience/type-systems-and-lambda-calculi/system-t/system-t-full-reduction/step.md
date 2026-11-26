# Full reduction of System T

Write $b[a]$ for the instantiation of the newest variable of
an abstraction body $b$ with $a$, and $\mathsf{R}\,u\,v\,t$ for the recursor. One-step reduction
$t \to t'$ between terms of the same type in the same context is the least relation closed under
these rules: $(\lambda b)\,a \to b[a]$; $\mathsf{R}\,u\,v\,\mathsf{zero} \to u$;
$\mathsf{R}\,u\,v\,(\mathsf{succ}\,t) \to v\,(\mathsf{R}\,u\,v\,t)\,t$; and reduction of any
immediate subterm: the function or the argument of an application, the body of an abstraction,
the argument of a successor, and each of the three arguments of the recursor
(Girard-Lafont-Taylor §7.1.4, Sørensen-Urzyczyn Definition 11.6.1).
