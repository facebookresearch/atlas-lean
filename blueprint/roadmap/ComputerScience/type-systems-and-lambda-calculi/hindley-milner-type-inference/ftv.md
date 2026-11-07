# Free type variables of a context

The free type variables of a typing context $\Gamma$
are the type variables occurring free in the visible scheme of some name bound in $\Gamma$.

A binding shadowed by an earlier binding of the same name does not count, so the free type
variables of $\Gamma$ depend only on the visible scheme of each name.
