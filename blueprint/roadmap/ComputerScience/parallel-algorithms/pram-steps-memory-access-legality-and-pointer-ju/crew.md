# CREW legality of a PRAM step

A PRAM step $s$ is CREW-legal (concurrent read, exclusive write) when, for all processors $i, j$, if $\mathrm{writeAddr}(i) = \mathrm{writeAddr}(j)$ then either $\mathrm{writeAddr}(i)$ is none or $i = j$. Reads are unconstrained.
