# PRAM program step

A synchronous PRAM program step with $p$ processors on a shared memory $\mathbb{N} \to \alpha$ consists of:

- a read address $\mathrm{readAddr}(i) \in \mathbb{N}$ for each processor $i \in \mathrm{Fin}\,p$;
- a computation $\mathrm{compute}(i) : \alpha \to \alpha$ applied to the value read;
- an optional write address $\mathrm{writeAddr}(i)$, either an address in $\mathbb{N}$ or none (the processor does not write).

Processor $i$ reads cell $\mathrm{readAddr}(i)$, applies $\mathrm{compute}(i)$ to the value read, and writes the result to $\mathrm{writeAddr}(i)$ if it is present.
