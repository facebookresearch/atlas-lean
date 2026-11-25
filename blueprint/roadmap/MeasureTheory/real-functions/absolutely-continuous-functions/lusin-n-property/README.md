# Absolutely continuous functions have the Lusin N property

Let $f : \mathbb{R} \to \mathbb{R}$ be absolutely continuous on every closed bounded interval. Then
$f$ maps Lebesgue null sets to null sets: for every set $s \subseteq \mathbb{R}$ of Lebesgue outer
measure $0$, the image $f(s)$ has Lebesgue outer measure $0$.

## Idea

Cover the part of a null set $s$ in a bounded interval by countably many disjoint open intervals of
total length less than $\delta$; absolute continuity makes the oscillations of $f$ on these
intervals add up to less than $\varepsilon$, and they bound the lengths of intervals covering the
image. Continuity alone is not enough: the Cantor function maps the null Cantor set onto $[0, 1]$.
Conversely, a continuous function of bounded variation with the Lusin N property is absolutely
continuous, by the Banach–Zarecki theorem.

## Statements

- [Absolutely continuous functions have the Lusin N property](volume-image-eq-zero-of-absolutely-conti.md)

## Background

- [Absolute continuity on an interval](../absolute-continuity-on-an-interval/README.md): the definition
