# Writers of a memory cell in a PRAM step

For a PRAM step $s$ with $p$ processors and an address $a \in \mathbb{N}$, the writers of $a$ are the finite set of processors $i \in \mathrm{Fin}\,p$ whose write address is $a$, that is, $\mathrm{writeAddr}(i) = a$.
