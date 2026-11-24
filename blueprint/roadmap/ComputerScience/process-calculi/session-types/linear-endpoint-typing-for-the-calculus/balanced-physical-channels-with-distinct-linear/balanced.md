# Balanced endpoint ownership

An ownership context $\Delta$ (a finite map from endpoints $x^{r}$, a name $x$ with polarity $r \in
\{+,-\}$, to capabilities $(k,S)$ of rank $k$ and protocol $S$) is balanced when for every endpoint
$e$ and capability $c$ with $\Delta(e) = c$, also $\Delta(\bar e) = \bar c$, where $\bar e$ is the
endpoint with the same name and the opposite polarity and $\bar c = (k,\overline{S})$ has the same
rank and the dual protocol. Balance alone does not exclude deadlocks.
