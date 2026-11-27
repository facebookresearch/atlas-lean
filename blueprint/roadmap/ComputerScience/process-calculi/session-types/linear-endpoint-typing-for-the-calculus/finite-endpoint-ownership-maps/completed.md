# Completed ownership map

An ownership context $\Delta$ (a finite map from endpoints to capabilities) is completed when for
every endpoint $e$ and capability $c = (k,S)$ with $\Delta(e) = c$, the head $\mathrm{unf}(S)$ of
$S$ is $\mathrm{end}$; the head of a protocol is its first action, or $\mathrm{end}$, after
unrolling a recursive protocol presented by a finite graph once. Entries with completed protocols
may remain in $\Delta$.
