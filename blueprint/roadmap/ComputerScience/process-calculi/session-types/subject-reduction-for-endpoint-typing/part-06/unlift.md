# Endpoint typing reflects through binder lifting

Let $n$ be a natural number, $\Gamma$ an ownership context none of whose endpoints has the name
$\mathrm{v}_0$, and $q$ a process. If $\Gamma \vdash_{n+1} \uparrow_0 q$ (endpoint typing), then
$\downarrow\Gamma \vdash_n q$, where $\downarrow\Gamma$ lowers every variable index of an endpoint
name by one.
