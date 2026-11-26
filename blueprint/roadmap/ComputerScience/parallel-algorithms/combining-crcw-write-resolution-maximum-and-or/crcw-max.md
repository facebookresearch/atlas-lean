# Maximum-rule CRCW write resolution

In a combining CRCW PRAM with $n$ processors, let $w : \mathrm{Fin}\,n \to \mathbb{N}$ give the natural number written by each processor to one shared cell. The maximum rule stores the finite supremum of the written values in $\mathbb{N}$:

$$\mathrm{crcwMax}(w) = \sup_{i \in \mathrm{Fin}\,n} w_i .$$

With no processors ($n = 0$) the value is $0$, the supremum of the empty family in $\mathbb{N}$.
