# Tail-area fdr is the posterior null probability given a region

In a [two-groups model](two-groups-model.md), for every measurable $\Gamma \subseteq \mathbb{R}$, under the [joint law](joint-law.md) of $(H, Z)$,

$$P(H = 0 \mid Z \in \Gamma) = \operatorname{Fdr}(\Gamma):$$

the [tail-area false discovery rate](tail-fdr.md) is the posterior null probability given $Z \in \Gamma$ (Storey 2002, Theorem 1; Efron 2010, Chapter 2). Both sides are $0$ when $P(Z \in \Gamma) = 0$ (the conditional probability given a null event is $0$ by convention).
