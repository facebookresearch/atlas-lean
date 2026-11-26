# Persistent service offer on a given name

Let $s$ be a natural number. A process offers $\mathrm{c}_s$ persistently if it is a replication
$!p$ such that $p$ has an unguarded input on $\mathrm{c}_s$ (an input on $\mathrm{c}_s$ reachable
through $\mid$, $\nu$ and replication only), or a parallel composition one of whose components
offers $\mathrm{c}_s$ persistently, or a restriction $\nu\,p$ such that $p$ does. $\mathbf{0}$,
inputs, outputs and choices do not.
