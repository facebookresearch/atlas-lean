# With one color the van der Waerden number is the progression length

For every natural $k>0$, the [van der Waerden forcing number](van-der-waerden-forcing-number.md) satisfies $W(1,k)=k$. The statement does not assign a value at $k=0$.

## Depends on

- [Van der Waerden forcing number](van-der-waerden-forcing-number.md).

## Proof outline

- A step-one progression fills the interval of size $k$, and the positive-step endpoint inequality forces every containing interval to have size at least $k$.

## Sources

- OpenAI, [Minimum size containing a progression](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Combinatorics/ProgressionColoring/Basic.lean#L59-L64), [Subsingleton coloring](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Combinatorics/ProgressionColoring/Basic.lean#L100-L104), and [One-color boundary value](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Combinatorics/ProgressionColoring/Basic.lean#L171-L176).
