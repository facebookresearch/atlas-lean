# OR-rule CRCW write resolution

In a combining CRCW PRAM with $n$ processors, let $w : \mathrm{Fin}\,n \to \mathrm{Bool}$ give the Boolean value written by each processor to one shared cell. The OR rule stores the finite supremum of the written values in the Boolean lattice ($\mathrm{false} < \mathrm{true}$), that is, their disjunction:

$$\mathrm{crcwOr}(w) = \bigvee_{i \in \mathrm{Fin}\,n} w_i .$$

With no processors ($n = 0$) the value is $\mathrm{false}$.
