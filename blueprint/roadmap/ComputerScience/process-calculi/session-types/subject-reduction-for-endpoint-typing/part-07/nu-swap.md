# Swapping nested restrictions preserves endpoint typing

Let $n$ be a natural number, $\Delta$ an ownership context and $p$ a process. If $\Delta \vdash_n
\nu\,\nu\,p$, then $\Delta \vdash_n \nu\,\nu\,(p[0 \leftrightarrow 1])$, where $p[0 \leftrightarrow
1]$ exchanges the names $\mathrm{v}_0$ and $\mathrm{v}_1$ of $p$ (the indices being raised by one
under each binder).
