# The two-term van der Waerden number is the number of colors plus one

For every natural $r>0$, the [van der Waerden forcing number](van-der-waerden-forcing-number.md) satisfies $W(r,2)=r+1$. Positivity of the number of colors is a hypothesis.

## Depends on

- [Van der Waerden forcing number](van-der-waerden-forcing-number.md).

## Proof outline

- The residue coloring is injective on the interval of size $r$, and on $r+1$ positions any $r$-coloring repeats a color at two different positions; their distance is a positive common difference.

## Sources

- OpenAI, [Two-term boundary value](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Combinatorics/ProgressionColoring/UpperBound.lean#L289-L302).
