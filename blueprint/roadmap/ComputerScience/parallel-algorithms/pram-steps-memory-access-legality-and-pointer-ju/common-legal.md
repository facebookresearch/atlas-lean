# CRCW-Common legality of a PRAM step

For a memory $\mathit{mem} : \mathbb{N} \to \alpha$, a PRAM step $s$ is CRCW-Common-legal when, for every address $a$ and all writers $i, j$ of $a$, $\mathrm{writeVal}(\mathit{mem}, s, i) = \mathrm{writeVal}(\mathit{mem}, s, j)$: all writers to a cell computed the same value. The condition depends on the memory.
