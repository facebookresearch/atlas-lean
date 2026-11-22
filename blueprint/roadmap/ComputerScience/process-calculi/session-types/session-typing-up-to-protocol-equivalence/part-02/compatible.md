# Semantic peer compatibility of an ownership map

An ownership context $\Delta$ is semantically compatible when for every endpoint $e$ and
capabilities $c$, $d$ with $\Delta(e) = c$ and $\Delta(\bar e) = d$ we have $d \approx \bar c$: the
two capabilities have the same rank and the protocol of $d$ is tree-equivalent to the dual of the
protocol of $c$. Here $\bar e$ is the endpoint with the name of $e$ and the opposite polarity.
