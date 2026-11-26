# Logarithmic volume bound for dense tube directions in dimension three

There is a real $c>0$ such that for every natural $m$, real $0<\delta\le1$, and unit directions $v_i$ and unrestricted centers $x_i$ in $\mathbb R^3$, if $|v_i-v_j|\ge\delta$ for all $i\ne j$ and $m\delta^2\ge1$, then the finite union of $T_i=\bigcup_{-1/2\le t\le1/2}B(x_i+tv_i,\delta)$ has real Lebesgue volume at least

$$
\frac{c}{(1+\log(1/\delta))^{66}}.
$$

The balls are open, the directions are tested as unit vectors, and the separation scale is the actual radius.

## Depends on

Unit segments and their open tube neighborhoods as in the statement.

## Proof depends on

- [Arbitrary-dimensional logarithmic union estimate](logarithmic-volume-bound-for-separated-tubes.md).

## Proof outline

Specialize to $n=3$, evaluate $2n(2n+5)=66$, and discard the factor $m\delta^2$ using the stated lower bound. The arbitrary-dimensional theorem remains a distinct stronger result.

## Sources

- OpenAI Math, [`tube_union_logarithmic_three_dimensional`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/MeasureTheory/Kakeya/Logarithmic.lean#L96-L101).
- [Family scope and accompanying paper](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/079.md).
- [Definitions in `Basic.lean`, lines 8–11](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Analysis/Fourier/Wave/Basic.lean#L8-L11).
- [Definitions in `Definitions.lean`, lines 13–20](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/MeasureTheory/Kakeya/Definitions.lean#L13-L20).
- [Definitions in `Logarithmic.lean`, lines 64–70](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/MeasureTheory/Kakeya/Logarithmic.lean#L64-L70).
