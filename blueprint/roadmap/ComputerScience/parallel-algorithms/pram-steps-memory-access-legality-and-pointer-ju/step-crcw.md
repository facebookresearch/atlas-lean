# Priority CRCW step function

For a memory $\mathit{mem} : \mathbb{N} \to \alpha$ and a PRAM step $s$ with $p$ processors, the new contents of cell $a$ are: if the set of writers of $a$ is nonempty, the value $\mathrm{writeVal}(\mathit{mem}, s, i)$ of the writer $i$ with the least index; otherwise the old value $\mathit{mem}(a)$. This is the Priority CRCW rule. On steps legal for CRCW-Common (all writers agree) or for CREW (at most one writer per cell), it gives the semantics of that discipline.
