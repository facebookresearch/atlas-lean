# Denotation of PCF terms

The denotation of a PCF term $t$ of type $A$ in a context $\Gamma$
is the Scott-continuous map $[\![t]\!]$ from environments for $\Gamma$ to the domain of $A$,
defined by recursion on $t$: a variable denotes its lookup map; $[\![\lambda t]\!]$ is the
currying of $[\![t]\!]$; $[\![f\,a]\!]\eta = [\![f]\!]\eta\,([\![a]\!]\eta)$;
$[\![\mathsf{zero}]\!]$ is constantly the defined value $0$; $[\![\mathsf{succ}\,t]\!]\eta$ and
$[\![\mathsf{pred}\,t]\!]\eta$ apply $n \mapsto n + 1$ and the predecessor map (with $0 \mapsto 0$)
to the partial natural number $[\![t]\!]\eta$, and are undefined where it is undefined;
$[\![\mathsf{ifz}\,t\,s_1\,s_2]\!]$ is the strict zero test of $[\![t]\!]$, $[\![s_1]\!]$,
$[\![s_2]\!]$; and $[\![\mathsf{fix}\,t]\!]\eta$ is the least fixed point of the continuous map
$[\![t]\!]\eta$.
