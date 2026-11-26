# Runtime typing reflects through binder lifting

Let $n$ be a natural number, $\Gamma$ a service environment, $\Delta$ an ownership context none of
whose endpoints has the name $\mathrm{v}_0$, and $q$ a process. If $\Gamma; \Delta \vdash_{n+1}
\uparrow_0 q$, then $\Gamma; \downarrow\Delta \vdash_n q$, where $\downarrow\Delta$ lowers the index
of every variable name of an endpoint of $\Delta$ by one.
