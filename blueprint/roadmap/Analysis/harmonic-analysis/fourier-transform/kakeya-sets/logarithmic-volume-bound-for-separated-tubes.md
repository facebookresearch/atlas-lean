# Logarithmic lower bound for the union of separated unit tubes

For each natural $n\ge2$ there is a real $c>0$ with the following property for every natural $m$, every real $0<\delta\le1$, and any unit vectors $v_i$ and centers $x_i$ in $\mathbb R^n$ indexed by $i\in\{0,\ldots,m-1\}$. Require $|v_i-v_j|\ge\delta$ for distinct indices. Define $T_i=\bigcup_{-1/2\le t\le1/2}B(x_i+tv_i,\delta)$ with **open** balls. Then

$$
\operatorname{vol}\left(\bigcup_i T_i\right)\ge
\frac{c m\delta^{n-1}}{(1+\log(1/\delta))^{2n(2n+5)}}.
$$

Volume is the real conversion of Lebesgue measure, finite here. The distance of directions is their Euclidean distance as unit vectors, not distance between unoriented lines. The centers are unrestricted, and no lower bound on $m$ is assumed.

## Depends on

The open radius-$\delta$ neighborhood of a closed unit core segment, finite indexed unions, and Euclidean direction separation.

## Proof depends on

- [Critical logarithmic local smoothing](../restriction-and-smoothing/endpoint-wave-estimates/critical-frequency-local-smoothing-logarithmic-loss.md).

Derive the localized logarithmic restriction and tube extension estimate, then transfer to global occupied volume without restrictions on the centers.

## Expansion

Split the logarithmic extension transfer and global localization from the final comparison at half scale. The intermediate union uses twice its auxiliary radius; substitute $\delta/2$ so the final tubes have actual radius $\delta$. Track $2n(2n+5)$ independently of the family size.

## Sources

- OpenAI Math, [`tube_union_logarithmic`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/MeasureTheory/Kakeya/Logarithmic.lean#L64-L70).
- [Family scope and accompanying paper](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/079.md).
- [Definitions in `Definitions.lean`, lines 68–79](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Analysis/Fourier/LocalSmoothing/Definitions.lean#L68-L79).
- [Definitions in `Basic.lean`, lines 8–11](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Analysis/Fourier/Wave/Basic.lean#L8-L11).
- [Definitions in `Definitions.lean`, lines 13–20](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/MeasureTheory/Kakeya/Definitions.lean#L13-L20).
- [Definitions in `Logarithmic.lean`, lines 13–58](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/MeasureTheory/Kakeya/Logarithmic.lean#L13-L58).
