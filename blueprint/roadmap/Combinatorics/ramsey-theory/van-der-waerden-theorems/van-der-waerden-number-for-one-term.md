# The one-term van der Waerden number is one

For every natural number $r$, the [van der Waerden forcing number](van-der-waerden-forcing-number.md) satisfies $W(r,1)=1$. This includes $r=0$: the universally quantified forcing condition on colorings into $[0]$ holds vacuously, and the infimum still ranges over positive interval sizes.

## Depends on

- [Van der Waerden forcing number](van-der-waerden-forcing-number.md).

## Proof outline

- Interval length one forces a one-term progression; use $a=0,d=1$ for any given coloring. The positive-size convention excludes zero.

## Sources

- OpenAI, [One term is forced in the first cell](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Combinatorics/ProgressionColoring/Basic.lean#L93-L98) and [One-term boundary value](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Combinatorics/ProgressionColoring/Basic.lean#L166-L169).
