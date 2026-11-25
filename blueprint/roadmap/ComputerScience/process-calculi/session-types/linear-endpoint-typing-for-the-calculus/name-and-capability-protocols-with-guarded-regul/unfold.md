# One-step unrolling of a protocol

The head $\mathrm{unf}(S)$ of a protocol $S$ is $S$ itself unless $S$ is a graph cursor $\langle
G,i,b\rangle$. For a cursor, write $\star = {?}$ if $b$ is true and $\star = {!}$ otherwise, and
$\bar\star$ for the other symbol; then $\mathrm{unf}\langle G,i,b\rangle$ is determined by the node
$i$ of $G$:

- an $\mathrm{end}$ node gives $\mathrm{end}$;
- a name send with successor $j$ gives $\star\mathrm{N}.\langle G,j,b\rangle$, a name receive gives
  $\bar\star\mathrm{N}.\langle G,j,b\rangle$;
- an endpoint send with polarity $r$, rank $k$, payload node $t$, payload flag $t_b$ and successor
  $j$ gives $\star(r,k,\langle G,t,t_b\rangle).\langle G,j,b\rangle$, and the corresponding endpoint
  receive gives $\bar\star(r,k,\langle G,t,t_b\rangle).\langle G,j,b\rangle$.

The payload keeps its own orientation flag $t_b$.
