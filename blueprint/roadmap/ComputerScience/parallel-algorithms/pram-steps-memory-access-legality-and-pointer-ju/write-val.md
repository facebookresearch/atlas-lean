# Value written by a PRAM processor

For a memory $\mathit{mem} : \mathbb{N} \to \alpha$, a PRAM step $s$ and a processor $i$, the value $i$ would write is

$$\mathrm{writeVal}(\mathit{mem}, s, i) = \mathrm{compute}(i)\big(\mathit{mem}(\mathrm{readAddr}(i))\big).$$

It is defined whether or not $i$ has a write address.
