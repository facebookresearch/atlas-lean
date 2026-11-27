# The Courtade–Kumar inequality and coordinate attainment

Let $n\ge1$, let $X$ be uniform on $\{0,1\}^n$, and obtain $Y$ by flipping each coordinate independently with probability $\varepsilon\in[0,1/2]$. For every Boolean function $f$, the mutual information in bits satisfies $I(f(X);Y)\le1-h_2(\varepsilon)$, where $h_2(t)=-[t\log t+(1-t)\log(1-t)]/\log2$ and $0\log0=0$.

For each coordinate $i$, both $f(x)=x_i$ and $f(x)=1-x_i$ attain equality. No assertion classifies the maximizers. In particular equality is possible for all functions at the endpoint $\varepsilon=1/2$.

**Conventions.** Use the joint mass $2^{-n}\sum_{x:f(x)=b}\varepsilon^{d_H(x,y)}(1-\varepsilon)^{n-d_H(x,y)}$, interpreting its factors as the independent per-coordinate probabilities. Use the two induced marginals and omit zero joint atoms in the logarithmic mutual-information sum. The finite mutual-information model supports the bits conversion.

## Depends on

- [Binary-cube bit noise and the sign-convention noise operator](bernoulli-cube-noise.md)

## Proof depends on

- [Sharp binary-channel contraction on the cube](sharp-binary-channel-contraction.md)

## Proof outline

Separate the uniform upper bound and the two coordinate cases. For the bound, take the signed Boolean function in the contraction theorem and convert from correlation $1-2\varepsilon$ and nats to crossover and bits. For attainment, the selected coordinate is uniform, its posterior crossover is exactly $\varepsilon$, and the other noisy coordinates are independent of the selected input and output pair. Check zero atoms separately at the noiseless endpoint.

## Sources

- [Pinned source statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/CourtadeKumar.lean#L69-L71)
- [Scope of the source formalization](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/119.md)
- [Accompanying manuscript: Sharp binary-information contraction on the discrete cube](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/Sharp-binary-information-contraction-on-the-discrete-cube-September-24-2026/main.pdf)
- [Background: Courtade and Kumar, *Which Boolean Functions Maximize Mutual Information on Noisy Inputs?* (2014)](https://doi.org/10.1109/TIT.2014.2326877)
