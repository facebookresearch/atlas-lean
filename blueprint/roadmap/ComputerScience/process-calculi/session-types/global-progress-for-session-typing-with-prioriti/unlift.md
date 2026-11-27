# Ranked typing descends from a lifted process

Let $n$ be a natural number, $\Gamma$ an ownership context none of whose endpoints has the name
$\mathrm{v}_0$, and $q$ a process. If $\Gamma \vdash^{\mathrm{rk}}_{n+1} \uparrow_0 q$, where
$\uparrow_0$ adds one to every free variable index, then $\downarrow\Gamma \vdash^{\mathrm{rk}}_n
q$, where $\downarrow\Gamma$ is obtained from $\Gamma$ by lowering the index of every variable name
of an endpoint by one.
