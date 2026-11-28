# Exact complex DFT circuits below every fixed n log n bound at arbitrarily large orders

For every real $c>0$ and natural $N_0\ge2$ there is an integer $n\ge N_0$ and a straight-line circuit computing the positive-sign complex discrete Fourier transform at order $n$, with strictly fewer than $c n\log_2 n$ gates. On input $(x_0,\ldots,x_{n-1})$, output $j$ is $\sum_k \exp(2\pi i/n)^{jk}x_k$ for every $j$ and all complex inputs.

Initially the $n$ input wires and a zero wire are available. A charged gate adds or subtracts two earlier wires or multiplies an earlier wire by an arbitrary fixed complex scalar. Values remain available and may be reused; outputs name available wires and are free. There is no coefficient magnitude or conditioning restriction. The quantified improvement is at arbitrarily large orders, not a single uniform program or a bound at every sufficiently large order in this gate model.

## Depends on

- [Finite DFT sum](dft-sum.md), with the character specialized to $\exp(2\pi i/n)$, and the charged scalar gate model above.

## Proof depends on

- An explicit family or unbounded sequence of lengths admitting exact circuits with normalized cost tending to zero; neither the standard FFT recurrence nor an arbitrary root-oracle RAM bound is such a gate certificate.

## Expansion

Define the scalar linear DAG with charge for scalar multiplication and prove the matrix-action correctness. Extract the quantitative sequence and show strict separation for every $c>0$ after every $N_0$. Do not identify this model with free scaled readouts or with uniform index arithmetic.

## Sources

- OpenAI, [ExactFourier.lean, scalar gates, positive-sign DFT and `main_theorem`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/ExactFourier.lean#L12-L58).
