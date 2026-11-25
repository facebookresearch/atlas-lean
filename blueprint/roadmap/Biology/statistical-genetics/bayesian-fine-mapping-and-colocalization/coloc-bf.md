# Bayes factor of a colocalization configuration

Let $\iota$ be a set of variants and let $\mathrm{BF}^{(1)}, \mathrm{BF}^{(2)} : \iota \to \mathbb{R}$ be per-variant Bayes factors for traits 1 and 2. The Bayes factor of a [configuration](coloc-hypothesis-2.md) $S = (a, b) \in \iota_\ast \times \iota_\ast$ is

$$\mathrm{BF}(S) = \beta_1(a)\, \beta_2(b), \qquad \beta_i(c) = \begin{cases} \mathrm{BF}^{(i)}_c & c \in \iota,\\ 1 & c = \ast. \end{cases}$$

It is the product of the two traits' Bayes factors against the null, a trait without a causal variant contributing $1$; the product form reflects independent studies of the two traits.
