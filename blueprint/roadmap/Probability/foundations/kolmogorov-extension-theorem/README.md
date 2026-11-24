# Kolmogorov extension theorem

Let $(\alpha_i)_{i \in \iota}$ be a family of Polish spaces, each with its Borel σ-algebra, indexed by an arbitrary set $\iota$. For each finite set $J \subseteq \iota$ let $P_J$ be a probability measure on $\prod_{j \in J} \alpha_j$, and suppose the family is projective: whenever $J \subseteq I$ are finite, the image of $P_I$ under the restriction map $\prod_{i \in I} \alpha_i \to \prod_{j \in J} \alpha_j$ is $P_J$. Then there is a measure $\mu$ on $\prod_{i \in \iota} \alpha_i$, with the product σ-algebra, whose image under the restriction map to $\prod_{j \in J} \alpha_j$ is $P_J$ for every finite $J \subseteq \iota$.

## Idea

A stochastic process $(X_i)_{i \in \iota}$ is often described only through its finite-dimensional distributions, the laws of the vectors $(X_j)_{j \in J}$ for finite $J$. These laws must be consistent with one another; the theorem says that, for Polish state spaces, consistency is also enough for a process with these laws to exist. It gives infinite product measures, Markov chains with given transition kernels, and Gaussian processes with a given covariance function, Brownian motion among them. The measure is defined on cylinder sets through the $P_J$; the work is to show countable additivity there, which uses that probability measures on Polish spaces are inner regular by compact sets, before extending to the product σ-algebra. Taking $J$ empty shows that $\mu$ has total mass $1$. Some regularity of the factors is needed: on general measurable spaces the conclusion can fail.

## Statements

- [Kolmogorov extension theorem](kolmogorov-extension.md)

## Background

- [Kolmogorov's extension theorem for sequences](../kolmogorov-extension-theorem-for-sequences/README.md): the classical case of real sequences, with uniqueness
