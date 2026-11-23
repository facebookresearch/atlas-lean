# Runtime inputs are active linear or have completed ownership

Let $n$ be a natural number, $\Gamma$ a service environment, $\Delta$ an ownership context, $a$ a
name and $p$ a process with $\Gamma; \Delta \vdash_n a(\cdot).p$. Then either there are an endpoint
$e$ with name $a$ and a capability $c$ of rank $k$ with $\Delta(e) = c$, the protocol of $c$ not
having head $\mathrm{end}$, and $\mathrm{Min}_\Delta(e,k)$; or every capability of $\Delta$ has head
$\mathrm{end}$.
