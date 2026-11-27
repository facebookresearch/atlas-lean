# Request-free runtime outputs have an active linear subject

Let $n$ be a natural number, $\Gamma$ a service environment, $\Delta$ an ownership context, $a$, $b$
names and $p$ a process with $\Gamma; \Delta \vdash_n \overline{a}\langle b\rangle.p$, where $a$ is
not a declared trigger. Then there are an endpoint $e$ with name $a$ and a capability $c$ of rank
$k$ with $\Delta(e) = c$, the protocol of $c$ not having head $\mathrm{end}$, and
$\mathrm{Min}_\Delta(e,k)$ (every other active endpoint of $\Delta$ has rank $> k$).
