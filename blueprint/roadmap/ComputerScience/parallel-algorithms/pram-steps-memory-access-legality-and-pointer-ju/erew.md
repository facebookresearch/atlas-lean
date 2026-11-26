# EREW legality of a PRAM step

A PRAM step $s$ is EREW-legal (exclusive read, exclusive write) when no two processors read the same cell and no two write the same cell: the read-address map $i \mapsto \mathrm{readAddr}(i)$ is injective, and for all processors $i, j$, if $\mathrm{writeAddr}(i) = \mathrm{writeAddr}(j)$ then either $\mathrm{writeAddr}(i)$ is none or $i = j$.
