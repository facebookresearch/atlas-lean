# Prokhorov's theorem on the real line

A sequence $(\mu_n)$ of probability measures on $\mathbb{R}$ is tight if and only if every subsequence of $(\mu_n)$ has a further subsequence converging weakly to a probability measure on $\mathbb{R}$.

## Idea

Prokhorov's theorem identifies tightness with relative sequential compactness for weak convergence. On the real line the forward direction comes from Helly's selection theorem: a subsequence of the distribution functions converges at the continuity points of a nondecreasing right-continuous limit $G$, and tightness forces $G$ to tend to $0$ at $-\infty$ and to $1$ at $+\infty$, so $G$ is the distribution function of a probability measure, the weak limit. Conversely, if the sequence is not tight, some $\varepsilon > 0$ and a subsequence put mass more than $\varepsilon$ outside $[-k, k]$ at stage $k$; a weak limit of a further subsequence would then give mass at least $\varepsilon$ outside every bounded interval, which no probability measure does. The theorem holds more generally on Polish spaces.

## Statements

- [Prokhorov's theorem, sequential form on $\mathbb{R}$](prokhorov-sequential.md)

## Background

- [Tight families of probability measures](../tightness-of-probability-measures/README.md)
- [Helly's selection theorem](../helly-s-selection-theorem/README.md)
