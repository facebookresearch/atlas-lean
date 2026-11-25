# Finite endpoint ownership map

An ownership context is a finite partial map $\Delta$ from endpoints to capabilities. An endpoint
$x^{r}$ is a π-calculus name $x$ together with a polarity $r \in \{+,-\}$, so the two endpoints
$x^{+}$ and $x^{-}$ of one name are distinct keys; a capability is a pair $(k,S)$ of a rank $k \in
\mathbb{N}$ and a protocol $S$. We write $\Delta(e) = c$ when $\Delta$ maps $e$ to $c$.
