# Design matrix for a full two-level factorial experiment

With $k$ factors and $r$ replicates of each treatment, a run is a pair $(x,a)$: $x$ assigns a level to every factor and $a$ indexes the replicate. Code the low and high levels as $-1$ and $+1$, respectively. For each subset $S$ of the factors, set

$$X_{(x,a),S}=\prod_{i\in S}\operatorname{code}(x_i).$$

The empty product makes the intercept column identically one. The other columns represent main effects and interactions. The definition also permits $r=0$, in which case there are no rows; the [least-squares formulas](factorial-effects-from-plus-minus-coding.md) require $r>0$.
