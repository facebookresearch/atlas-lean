# Lowering a lifted process preserves conversion typing

Let $n$ be a natural number, $\Gamma$ an ownership context none of whose endpoints has the name
$\mathrm{v}_0$, and $q$ a process. If $\Gamma \vdash^{\simeq}_{n+1} \uparrow_0 q$, where
$\uparrow_0$ adds one to every free variable index, then $\downarrow\Gamma \vdash^{\simeq}_n q$,
where $\downarrow\Gamma$ lowers the index of every variable name of an endpoint of $\Gamma$ by one.
